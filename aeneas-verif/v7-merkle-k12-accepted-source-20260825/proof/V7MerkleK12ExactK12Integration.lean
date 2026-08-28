import V7MerkleK12CallerBridge
import AspisFormal.K1.V7Tag73ExactConcreteK12Bound

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Literal Tag-73 Merkle caller to the maintained exact K1.2 obligation

The Aeneas callback is a pure function, whereas the maintained ROM execution
stores an effectful, ordered SHA table and history.  Consequently a translated
caller run alone cannot state which callback invocations were inserted into
that history.  This module isolates precisely that runtime/tool boundary as
`SourceOpeningRuntimeReflection`: each successful leaf/node call already
present in the translated source path has its returned 208-bit prefix in the
exact ROM table and its raw input in the final shared history.

The boundary is deliberately below the K1.2 conclusion.  It contains neither
`accepted_two_tree_openings`, `TraceIncludedInLog`,
`ExactPrefixK12SuppliedCoverage`, extraction success, nor a probability claim.
Everything from reflected literal source calls to both fields of
`ExactTag73K12SourceObligations` is proved here.
-/

namespace AspisV7MerkleK12ExactK12Integration

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV7MerkleK12AcceptedBridge
open AspisV7MerkleK12CallerBridge
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactConcreteK12Bound

noncomputable section

/-! ## Source-path reflection into the maintained shared ROM -/

/-- Every nonempty constructor of a translated source path stores the literal
successful production `node_hash_v7` call.  Reflection says only that the
returned prefix agrees with the maintained ROM and that this exact raw input
occurs in its final ordered history. -/
def SourcePathRuntimeReflected
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) {hash : GeneratedHash} :
    {rounds : Nat} → {position rootPosition : Std.U32} →
    {digest root : GeneratedDigest} →
    GeneratedSourcePath hash rounds position digest rootPosition root → Prop
  | _, _, _, _, _, .zero _ _ => True
  | _, _, _, _, _, .left (digest := digest) (parent := parent)
      sibling _ _ _ tail =>
      truncateSha256 (serialize (.node
        (AspisV7MerkleK12LayoutBridge.digestFixed digest)
        (AspisV7MerkleK12LayoutBridge.digestFixed sibling))) =
          AspisV7MerkleK12LayoutBridge.digestFixed parent ∧
      serialize (.node
        (AspisV7MerkleK12LayoutBridge.digestFixed digest)
        (AspisV7MerkleK12LayoutBridge.digestFixed sibling)) ∈ log ∧
      SourcePathRuntimeReflected truncateSha256 log tail
  | _, _, _, _, _, .right (digest := digest) (parent := parent)
      sibling _ _ _ tail =>
      truncateSha256 (serialize (.node
        (AspisV7MerkleK12LayoutBridge.digestFixed sibling)
        (AspisV7MerkleK12LayoutBridge.digestFixed digest))) =
          AspisV7MerkleK12LayoutBridge.digestFixed parent ∧
      serialize (.node
        (AspisV7MerkleK12LayoutBridge.digestFixed sibling)
        (AspisV7MerkleK12LayoutBridge.digestFixed digest)) ∈ log ∧
      SourcePathRuntimeReflected truncateSha256 log tail

/-- Runtime reflection for the two leaf calls and both literal node-call
paths of one translated paired opening. -/
structure SourceOpeningRuntimeReflection
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) {hash : GeneratedHash}
    {c1Root c2Root : GeneratedDigest}
    (opening : PairedSourceOpening hash c1Root c2Root) : Prop where
  c1LeafExact :
    truncateSha256 (serialize (.c1Leaf
      (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 403) opening.c1Value)
      (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt))) =
        AspisV7MerkleK12LayoutBridge.digestFixed opening.c1Leaf
  c1LeafInHistory :
    serialize (.c1Leaf
      (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 403) opening.c1Value)
      (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt)) ∈ log
  c2LeafExact :
    truncateSha256 (serialize (.c2Leaf
      (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 186) opening.c2Value)
      (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt))) =
        AspisV7MerkleK12LayoutBridge.digestFixed opening.c2Leaf
  c2LeafInHistory :
    serialize (.c2Leaf
      (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 186) opening.c2Value)
      (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt)) ∈ log
  c1Path : SourcePathRuntimeReflected truncateSha256 log opening.c1Path
  c2Path : SourcePathRuntimeReflected truncateSha256 log opening.c2Path

theorem source_path_foldPathAux_of_runtime_reflected
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) {hash : GeneratedHash}
    {rounds : Nat} {position rootPosition : Std.U32}
    {digest root : GeneratedDigest}
    (path : GeneratedSourcePath hash rounds position digest rootPosition root)
    (reflected : SourcePathRuntimeReflected truncateSha256 log path) :
    foldPathAux truncateSha256 position.val
        (AspisV7MerkleK12LayoutBridge.digestFixed digest) path.siblingList =
      AspisV7MerkleK12LayoutBridge.digestFixed root := by
  induction path with
  | zero => rfl
  | left sibling positionEven parentPositionExact hashRun tail ih =>
      rcases reflected with ⟨stepExact, _stepInHistory, tailReflected⟩
      simp only [GeneratedSourcePath.siblingList, foldPathAux, positionEven,
        Bool.false_eq_true, ↓reduceIte]
      rw [stepExact, ← parentPositionExact]
      exact ih tailReflected
  | right sibling positionOdd parentPositionExact hashRun tail ih =>
      rcases reflected with ⟨stepExact, _stepInHistory, tailReflected⟩
      simp only [GeneratedSourcePath.siblingList, foldPathAux, positionOdd,
        ↓reduceIte]
      rw [stepExact, ← parentPositionExact]
      exact ih tailReflected

theorem source_path_foldPath_of_runtime_reflected
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) {hash : GeneratedHash}
    {position rootPosition : Std.U32} {digest root : GeneratedDigest}
    (positionBound : position.val < 2 ^ treeDepth)
    (path : GeneratedSourcePath hash treeDepth position digest rootPosition root)
    (reflected : SourcePathRuntimeReflected truncateSha256 log path) :
    foldPath truncateSha256 ⟨position.val, positionBound⟩
        (AspisV7MerkleK12LayoutBridge.digestFixed digest)
        path.siblingVector =
      AspisV7MerkleK12LayoutBridge.digestFixed root := by
  unfold foldPath
  rw [path.siblingVector_bytes]
  exact source_path_foldPathAux_of_runtime_reflected truncateSha256 log path
    reflected

theorem source_path_trace_covered_of_runtime_reflected
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) {hash : GeneratedHash}
    {rounds : Nat} {position rootPosition : Std.U32}
    {digest root : GeneratedDigest}
    (path : GeneratedSourcePath hash rounds position digest rootPosition root)
    (reflected : SourcePathRuntimeReflected truncateSha256 log path) :
    TraceIncludedInLog
      (foldPathInputTrace truncateSha256 position.val
        (AspisV7MerkleK12LayoutBridge.digestFixed digest) path.siblingList)
      log := by
  induction path with
  | zero =>
      intro input member
      simp [GeneratedSourcePath.siblingList, foldPathInputTrace] at member
  | left sibling positionEven parentPositionExact hashRun tail ih =>
      rcases reflected with ⟨stepExact, stepInHistory, tailReflected⟩
      intro input member
      simp only [GeneratedSourcePath.siblingList, foldPathInputTrace,
        List.mem_cons] at member
      rcases member with rfl | member
      · simpa [orderedNodeInput, positionEven] using stepInHistory
      · apply ih tailReflected input
        simpa [orderedNodeInput, positionEven, stepExact,
          parentPositionExact] using member
  | right sibling positionOdd parentPositionExact hashRun tail ih =>
      rcases reflected with ⟨stepExact, stepInHistory, tailReflected⟩
      intro input member
      simp only [GeneratedSourcePath.siblingList, foldPathInputTrace,
        List.mem_cons] at member
      rcases member with rfl | member
      · simpa [orderedNodeInput, positionOdd] using stepInHistory
      · apply ih tailReflected input
        simpa [orderedNodeInput, positionOdd, stepExact,
          parentPositionExact] using member

theorem SourceOpeningRuntimeReflection.authenticates
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) {hash : GeneratedHash}
    {c1Root c2Root : GeneratedDigest}
    (opening : PairedSourceOpening hash c1Root c2Root)
    (reflected : SourceOpeningRuntimeReflection truncateSha256 log opening) :
    foldPath truncateSha256 opening.toFrozenOpening.position
        (c1DisclosedLeafDigest truncateSha256 opening.toFrozenOpening)
        opening.toFrozenOpening.c1Siblings =
          AspisV7MerkleK12LayoutBridge.digestFixed c1Root ∧
      foldPath truncateSha256 opening.toFrozenOpening.position
        (c2DisclosedLeafDigest truncateSha256 opening.toFrozenOpening)
        opening.toFrozenOpening.c2Siblings =
          AspisV7MerkleK12LayoutBridge.digestFixed c2Root := by
  constructor
  · change foldPath truncateSha256 opening.finitePosition
      (truncateSha256 (serialize (.c1Leaf
        (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 403) opening.c1Value)
        (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt))))
      opening.c1Path.siblingVector = _
    rw [reflected.c1LeafExact]
    exact source_path_foldPath_of_runtime_reflected truncateSha256 log
      opening.positionBound opening.c1Path reflected.c1Path
  · change foldPath truncateSha256 opening.finitePosition
      (truncateSha256 (serialize (.c2Leaf
        (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 186) opening.c2Value)
        (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt))))
      opening.c2Path.siblingVector = _
    rw [reflected.c2LeafExact]
    exact source_path_foldPath_of_runtime_reflected truncateSha256 log
      opening.positionBound opening.c2Path reflected.c2Path

theorem SourceOpeningRuntimeReflection.c1_trace_covered
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) {hash : GeneratedHash}
    {c1Root c2Root : GeneratedDigest}
    (opening : PairedSourceOpening hash c1Root c2Root)
    (reflected : SourceOpeningRuntimeReflection truncateSha256 log opening) :
    TraceIncludedInLog
      (openingInputTrace truncateSha256 opening.toFrozenOpening.position
        (.c1Leaf opening.toFrozenOpening.c1Value
          opening.toFrozenOpening.sharedSalt)
        opening.toFrozenOpening.c1Siblings) log := by
  unfold openingInputTrace openingRawInputTrace
  change TraceIncludedInLog
    (serialize (.c1Leaf
      (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 403) opening.c1Value)
      (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt)) ::
      foldPathInputTrace truncateSha256 opening.position.val
        (truncateSha256 (serialize (.c1Leaf
          (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 403) opening.c1Value)
          (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt))))
        (List.ofFn opening.c1Path.siblingVector)) log
  rw [opening.c1Path.siblingVector_bytes]
  intro input member
  change input ∈
    serialize (.c1Leaf
      (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 403) opening.c1Value)
      (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt)) ::
      foldPathInputTrace truncateSha256 opening.position.val
        (truncateSha256 (serialize (.c1Leaf
          (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 403) opening.c1Value)
          (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt))))
        opening.c1Path.siblingList at member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact reflected.c1LeafInHistory
  · apply source_path_trace_covered_of_runtime_reflected truncateSha256
      log opening.c1Path reflected.c1Path input
    simpa [reflected.c1LeafExact] using member

theorem SourceOpeningRuntimeReflection.c2_trace_covered
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) {hash : GeneratedHash}
    {c1Root c2Root : GeneratedDigest}
    (opening : PairedSourceOpening hash c1Root c2Root)
    (reflected : SourceOpeningRuntimeReflection truncateSha256 log opening) :
    TraceIncludedInLog
      (openingInputTrace truncateSha256 opening.toFrozenOpening.position
        (.c2Leaf opening.toFrozenOpening.c2Value
          opening.toFrozenOpening.sharedSalt)
        opening.toFrozenOpening.c2Siblings) log := by
  unfold openingInputTrace openingRawInputTrace
  change TraceIncludedInLog
    (serialize (.c2Leaf
      (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 186) opening.c2Value)
      (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt)) ::
      foldPathInputTrace truncateSha256 opening.position.val
        (truncateSha256 (serialize (.c2Leaf
          (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 186) opening.c2Value)
          (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt))))
        (List.ofFn opening.c2Path.siblingVector)) log
  rw [opening.c2Path.siblingVector_bytes]
  intro input member
  change input ∈
    serialize (.c2Leaf
      (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 186) opening.c2Value)
      (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt)) ::
      foldPathInputTrace truncateSha256 opening.position.val
        (truncateSha256 (serialize (.c2Leaf
          (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 186) opening.c2Value)
          (AspisV7MerkleK12LayoutBridge.saltFixed opening.salt))))
        opening.c2Path.siblingList at member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact reflected.c2LeafInHistory
  · apply source_path_trace_covered_of_runtime_reflected truncateSha256
      log opening.c2Path reflected.c2Path input
    simpa [reflected.c2LeafExact] using member

/-! ## The exact source opening batch selected by literal caller control flow -/

noncomputable def sourceOpeningBatchOfCallerFlow
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    PairedSourceOpeningBatch hash wire.c1_root wire.c2_root := by
  let evidence := flow.acceptedTrace.terminalEvidence
  let traversal := exactTraversalOfCallerTrace hash wire powers flow.iterator
    callerInitialCombined output callerInitialEntries flow.seedBatch
    flow.acceptedTrace
  have entriesExact : evidence.terminalEntries.val =
      List.ofFn (fun ordinal => (flow.seedBatch ordinal).entry) := by
    rw [evidence.entriesExact]
    simp only [callerInitialEntries, alloc.vec.Vec.with_capacity,
      alloc.vec.Vec.new, List.nil_append]
    rw [List.map_ofFn]
    congr 1
  exact sourceOpeningBatchOfRounds flow.seedBatch
    traversal.initialization.seededLevel evidence.outputLevel
    (AspisV7MerkleK12OuterTraceBridge.outerEdgeTraceOfExactTraversal hash
      wire.c1_root wire.c2_root
      (alloc.vec.Vec.deref evidence.terminalEntries) wire.c1_frontier
      wire.c2_frontier
      (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
        V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
      (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
        V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
      evidence.outputLevel evidence.outputNext traversal).toPairedHashRounds
    (by
      rw [AspisV7MerkleK12TraversalBridge.exact_traversal_seeded_level_values
        hash wire.c1_root wire.c2_root 18#u32
        (alloc.vec.Vec.deref evidence.terminalEntries) wire.c1_frontier
        wire.c2_frontier
        (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
          V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
        (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
          V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
        evidence.outputLevel evidence.outputNext traversal]
      exact entriesExact)
    (AspisV7MerkleK12TraversalBridge.exact_traversal_final_level_values hash
      wire.c1_root wire.c2_root 18#u32
      (alloc.vec.Vec.deref evidence.terminalEntries) wire.c1_frontier
      wire.c2_frontier
      (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
        V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
      (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
        V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
      evidence.outputLevel evidence.outputNext traversal)

theorem sourceOpeningBatchOfCallerFlow_finitePosition
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output)
    (ordinal : Fin disclosedQueryPairs) :
    (sourceOpeningBatchOfCallerFlow flow ordinal).finitePosition =
      (flow.seedBatch ordinal).finitePosition := by
  unfold sourceOpeningBatchOfCallerFlow
  apply sourceOpeningBatchOfRounds_finitePosition

theorem source_opening_batch_accepted_of_runtime_reflection
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog)
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output)
    (reflected : ∀ ordinal,
      SourceOpeningRuntimeReflection truncateSha256 log
        (sourceOpeningBatchOfCallerFlow flow ordinal)) :
    accepted_two_tree_openings truncateSha256
      (rootsOfGeneratedDigests wire.c1_root wire.c2_root)
      (proofOfSourceOpeningBatch (sourceOpeningBatchOfCallerFlow flow)) := by
  constructor
  · have positionsNodup :
        (List.ofFn (fun ordinal =>
          (flow.seedBatch ordinal).finitePosition)).Nodup :=
      List.nodup_ofFn.mpr flow.seedBatch_positionsInjective
    change (List.ofFn (fun ordinal =>
      (sourceOpeningBatchOfCallerFlow flow ordinal).finitePosition)).Nodup
    simpa only [sourceOpeningBatchOfCallerFlow_finitePosition] using
      positionsNodup
  · intro ordinal
    exact (reflected ordinal).authenticates truncateSha256 log
      (sourceOpeningBatchOfCallerFlow flow ordinal)

theorem source_opening_batch_supplied_coverage_of_runtime_reflection
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog)
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output)
    (reflected : ∀ ordinal,
      SourceOpeningRuntimeReflection truncateSha256 log
        (sourceOpeningBatchOfCallerFlow flow ordinal)) :
    (∀ ordinal,
      TraceIncludedInLog
        (openingInputTrace truncateSha256
          (proofOfSourceOpeningBatch
            (sourceOpeningBatchOfCallerFlow flow) ordinal).position
          (.c1Leaf
            (proofOfSourceOpeningBatch
              (sourceOpeningBatchOfCallerFlow flow) ordinal).c1Value
            (proofOfSourceOpeningBatch
              (sourceOpeningBatchOfCallerFlow flow) ordinal).sharedSalt)
          (proofOfSourceOpeningBatch
            (sourceOpeningBatchOfCallerFlow flow) ordinal).c1Siblings) log) ∧
    (∀ ordinal,
      TraceIncludedInLog
        (openingInputTrace truncateSha256
          (proofOfSourceOpeningBatch
            (sourceOpeningBatchOfCallerFlow flow) ordinal).position
          (.c2Leaf
            (proofOfSourceOpeningBatch
              (sourceOpeningBatchOfCallerFlow flow) ordinal).c2Value
            (proofOfSourceOpeningBatch
              (sourceOpeningBatchOfCallerFlow flow) ordinal).sharedSalt)
          (proofOfSourceOpeningBatch
            (sourceOpeningBatchOfCallerFlow flow) ordinal).c2Siblings) log) := by
  constructor
  · intro ordinal
    exact (reflected ordinal).c1_trace_covered truncateSha256 log
      (sourceOpeningBatchOfCallerFlow flow ordinal)
  · intro ordinal
    exact (reflected ordinal).c2_trace_covered truncateSha256 log
      (sourceOpeningBatchOfCallerFlow flow ordinal)

/-! ## Literal production caller binding and exact K1.2 closure -/

/-- Data/control-flow binding for one maintained operational input.  The only
semantic field is `runtimeReflection`, which is the unavoidable bridge from
the pure translated callback to the separately modelled effectful shared ROM.
The proof/root equalities bind generated parser/caller values to the maintained
post-parser projections; they assert no acceptance or extraction conclusion. -/
structure LiteralCallerExactK12Binding
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) where
  hash : AspisV7MerkleK12SourceBridge.GeneratedHash
  wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire
  queries : Array Std.U32 16#usize
  powers :
    V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers
  output : CallerCombined
  callerRun :
    V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings
      hash wire queries powers = .ok (.Ok output)
  rootsExact :
    rootsOfGeneratedDigests wire.c1_root wire.c2_root = exactK12Roots input
  openingsExact :
    proofOfSourceOpeningBatch
      (sourceOpeningBatchOfCallerFlow
        (exactWrapperControlFlowOfCallerSuccess hash wire queries powers output
          callerRun)) = exactK12Openings input
  runtimeReflection : ∀ ordinal,
    SourceOpeningRuntimeReflection (exactK12Truncate input)
      (exactK12OrderedQueries input)
      (sourceOpeningBatchOfCallerFlow
        (exactWrapperControlFlowOfCallerSuccess hash wire queries powers output
          callerRun) ordinal)

theorem literal_caller_binding_implies_openings_accepted
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (binding : LiteralCallerExactK12Binding input) :
    accepted_two_tree_openings (exactK12Truncate input)
      (exactK12Roots input) (exactK12Openings input) := by
  let flow := exactWrapperControlFlowOfCallerSuccess binding.hash binding.wire
    binding.queries binding.powers binding.output binding.callerRun
  have accepted := source_opening_batch_accepted_of_runtime_reflection
    (exactK12Truncate input) (exactK12OrderedQueries input) flow
    binding.runtimeReflection
  dsimp only [flow] at accepted
  rw [binding.rootsExact, binding.openingsExact] at accepted
  exact accepted

theorem literal_caller_binding_implies_supplied_coverage
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (binding : LiteralCallerExactK12Binding input) :
    ExactPrefixK12SuppliedCoverage input := by
  let flow := exactWrapperControlFlowOfCallerSuccess binding.hash binding.wire
    binding.queries binding.powers binding.output binding.callerRun
  have covered := source_opening_batch_supplied_coverage_of_runtime_reflection
    (exactK12Truncate input) (exactK12OrderedQueries input) flow
    binding.runtimeReflection
  rw [binding.openingsExact] at covered
  exact covered

/-- Global source/runtime adapter.  This asks for one literal successful
translated caller binding for each actual accepted fixed-run input. -/
structure ExactTag73K12LiteralCallerSource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) : Prop where
  caller : ∀ (sample : ExactCompilerSample HiddenTape parameters)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample),
    Nonempty (LiteralCallerExactK12Binding input)

/-- Strongest composition theorem: literal translated production caller
success plus the explicit effectful-callback reflection constructs both exact
source obligations consumed by maintained K1.2. -/
theorem literal_production_callers_construct_exact_tag73_k12_source_obligations
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (source : ExactTag73K12LiteralCallerSource transitionFuel configuration
      projection fixedInstance) :
    ExactTag73K12SourceObligations transitionFuel configuration projection
      fixedInstance := by
  constructor
  · intro sample input
    exact literal_caller_binding_implies_openings_accepted
      (Classical.choice (source.caller sample input))
  · intro sample input
    exact literal_caller_binding_implies_supplied_coverage
      (Classical.choice (source.caller sample input))

#print axioms source_path_foldPathAux_of_runtime_reflected
#print axioms source_path_trace_covered_of_runtime_reflected
#print axioms SourceOpeningRuntimeReflection.authenticates
#print axioms SourceOpeningRuntimeReflection.c1_trace_covered
#print axioms SourceOpeningRuntimeReflection.c2_trace_covered
#print axioms source_opening_batch_accepted_of_runtime_reflection
#print axioms source_opening_batch_supplied_coverage_of_runtime_reflection
#print axioms literal_caller_binding_implies_openings_accepted
#print axioms literal_caller_binding_implies_supplied_coverage
#print axioms literal_production_callers_construct_exact_tag73_k12_source_obligations

end

end AspisV7MerkleK12ExactK12Integration
