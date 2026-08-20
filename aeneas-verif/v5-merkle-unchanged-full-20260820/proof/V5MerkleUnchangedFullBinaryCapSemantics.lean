import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullLevelTraceLists
import V5MerkleUnchangedFullFrontierChunks

/-! Exact model meaning of the unchanged odd-depth binary-cap check. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullBinaryCapSemantics

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFullTopologyAccessors
open AspisV5MerkleUnchangedFullRadixSoundness
open AspisV5MerkleUnchangedFullFrontierChunks

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

/-- The three possible accepted odd-cap layouts, stated entirely in model
digests and exact source order. -/
inductive ExactOddCapModelLocation
    (active : List Nat) (live frontier : List Digest32)
    (frontierOrdinal : Nat) : Digest32 → Digest32 → Prop
  | both (left right : Digest32)
      (active_exact : active = [0, 1])
      (live_exact : live = [left, right])
      (frontier_consumed : frontierOrdinal = frontier.length) :
      ExactOddCapModelLocation active live frontier frontierOrdinal left right
  | liveLeft (left right : Digest32)
      (active_exact : active = [0])
      (live_exact : live = [left])
      (frontier_bound : frontierOrdinal < frontier.length)
      (right_exact : right = frontier[frontierOrdinal])
      (frontier_consumed : frontierOrdinal + 1 = frontier.length) :
      ExactOddCapModelLocation active live frontier frontierOrdinal left right
  | liveRight (left right : Digest32)
      (active_exact : active = [1])
      (live_exact : live = [right])
      (frontier_bound : frontierOrdinal < frontier.length)
      (left_exact : left = frontier[frontierOrdinal])
      (frontier_consumed : frontierOrdinal + 1 = frontier.length) :
      ExactOddCapModelLocation active live frontier frontierOrdinal left right

/-- Model data exported by one accepted odd-cap source execution. -/
structure ExactOddBinaryCapData
    (sha256 : List ModelByte → Digest32) (root : Digest32)
    (active : List Nat) (live frontier : List Digest32)
    (frontierOrdinal : Nat) : Type where
  left : Digest32
  right : Digest32
  location : ExactOddCapModelLocation active live frontier frontierOrdinal
    left right
  root_eq : (sha256MerkleHashing sha256).binaryNode left right = root

private theorem slice_index_success_value
    (input : Slice α) (position : Std.Usize) (value : α)
    (hposition : position.val < input.val.length)
    (hrun : Slice.index_usize input position = .ok value) :
    value = input.val[position.val] := by
  obtain ⟨witness, hwitness, heq⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Slice.index_usize_spec input position hposition)
  have : witness = value := Result.ok.inj (hwitness.symm.trans hrun)
  exact this ▸ heq

private theorem as_slice_values_exact
    (values : GeneratedDigestVec) (slice : Slice GeneratedDigest)
    (hrun : alloc.vec.Vec.as_slice Global values = .ok slice) :
    slice.val = values.val := by
  unfold alloc.vec.Vec.as_slice at hrun
  exact congrArg Subtype.val (Result.ok.inj hrun) |>.symm

private theorem one_index_slice_exact
    (indices : Slice α) (index : α)
    (hlength : Slice.len indices = 1#usize)
    (hrun : Slice.index_usize indices 0#usize = .ok index) :
    indices.val = [index] := by
  have lengthExact : indices.val.length = 1 := by
    have := congrArg UScalar.val hlength
    simpa [Slice.len_val] using this
  have position : 0 < indices.val.length := by omega
  have headExact := slice_index_success_value indices 0#usize index position hrun
  apply List.ext_getElem
  · simpa [lengthExact]
  · intro ordinal leftBound rightBound
    have ordinalZero : ordinal = 0 := by omega
    subst ordinal
    simpa using headExact.symm

private theorem two_index_slice_exact
    (indices : Slice α) (left right : α)
    (hlength : Slice.len indices = 2#usize)
    (leftRun : Slice.index_usize indices 0#usize = .ok left)
    (rightRun : Slice.index_usize indices 1#usize = .ok right) :
    indices.val = [left, right] := by
  have lengthExact : indices.val.length = 2 := by
    have := congrArg UScalar.val hlength
    simpa [Slice.len_val] using this
  have leftPosition : 0 < indices.val.length := by omega
  have rightPosition : 1 < indices.val.length := by omega
  have leftExact := slice_index_success_value indices 0#usize left
    leftPosition leftRun
  have rightExact := slice_index_success_value indices 1#usize right
    rightPosition rightRun
  apply List.ext_getElem
  · simpa [lengthExact]
  · intro ordinal leftBound rightBound
    have ordinalBound : ordinal < 2 := by omega
    interval_cases ordinal
    · simpa using leftExact.symm
    · simpa using rightExact.symm

private theorem one_live_value_exact
    (level : GeneratedDigestVec) (levelSlice : Slice GeneratedDigest)
    (value : GeneratedDigest)
    (sliceRun : alloc.vec.Vec.as_slice Global level = .ok levelSlice)
    (hlength : Slice.len levelSlice = 1#usize)
    (valueRun : Slice.index_usize levelSlice 0#usize = .ok value) :
    level.val = [value] := by
  have sliceExact := one_index_slice_exact levelSlice value hlength valueRun
  rw [as_slice_values_exact level levelSlice sliceRun] at sliceExact
  exact sliceExact

private theorem two_live_values_exact
    (level : GeneratedDigestVec) (levelSlice : Slice GeneratedDigest)
    (left right : GeneratedDigest)
    (sliceRun : alloc.vec.Vec.as_slice Global level = .ok levelSlice)
    (hlength : Slice.len levelSlice = 2#usize)
    (leftRun : Slice.index_usize levelSlice 0#usize = .ok left)
    (rightRun : Slice.index_usize levelSlice 1#usize = .ok right) :
    level.val = [left, right] := by
  have sliceExact := two_index_slice_exact levelSlice left right hlength
    leftRun rightRun
  rw [as_slice_values_exact level levelSlice sliceRun] at sliceExact
  exact sliceExact

private theorem reified_frontier_length_exact
    (bytes : List Std.U8) (frontier : List Digest32)
    (hflat : frontier.flatMap digestBytes =
      bytes.map generatedU8ToByte) :
    bytes.length = 32 * frontier.length := by
  have lengths := congrArg List.length hflat
  simpa [List.length_flatMap, digestBytes_length, Nat.mul_comm] using
    lengths.symm

private theorem copied_sibling_slice_exact
    (nodeBytes : Slice Std.U8) (nodePos : Std.Usize)
    (siblingSlice : Slice Std.U8) (sibling : GeneratedDigest)
    (sliceRun : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) nodeBytes
      { start := nodePos,
        «end» := Std.Usize.wrapping_add nodePos 32#usize } =
      .ok siblingSlice)
    (copyRun : core.array.TryFromArrayCopySlice.try_from 32#usize
      core.marker.CopyU8 siblingSlice = .ok (.Ok sibling)) :
    sibling.val = List.slice nodePos.val
      (Std.Usize.wrapping_add nodePos 32#usize).val nodeBytes.val := by
  change core.slice.index.SliceIndexRangeUsizeSlice.index
    { start := nodePos,
      «end» := Std.Usize.wrapping_add nodePos 32#usize } nodeBytes =
      .ok siblingSlice at sliceRun
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at sliceRun
  split at sliceRun
  next bounds =>
    have sliceEq := Result.ok.inj sliceRun
    have sliceValues := congrArg Subtype.val sliceEq
    unfold core.array.TryFromArrayCopySlice.try_from at copyRun
    split at copyRun
    next exactLength =>
      have copyEq := Result.ok.inj copyRun
      injection copyEq with siblingEq
      exact (congrArg Subtype.val siblingEq).symm.trans sliceValues.symm
    next wrongLength => simp at copyRun
  next bounds => simp at sliceRun

private theorem usize_add_32_exact_of_slice
    (nodeBytes : Slice Std.U8) (nodePos : Std.Usize)
    (siblingSlice : Slice Std.U8)
    (sliceRun : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) nodeBytes
      { start := nodePos,
        «end» := Std.Usize.wrapping_add nodePos 32#usize } =
      .ok siblingSlice) :
    (Std.Usize.wrapping_add nodePos 32#usize).val = nodePos.val + 32 := by
  change core.slice.index.SliceIndexRangeUsizeSlice.index
    { start := nodePos,
      «end» := Std.Usize.wrapping_add nodePos 32#usize } nodeBytes =
      .ok siblingSlice at sliceRun
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at sliceRun
  split at sliceRun
  next bounds =>
    have startLeEnd : nodePos.val ≤
        (Std.Usize.wrapping_add nodePos 32#usize).val := by
      simpa only [UScalar.le_equiv] using bounds.1
    rw [Std.Usize.wrapping_add_val_eq] at startLeEnd ⊢
    norm_num at startLeEnd ⊢
    have valueBound : nodePos.val < Std.Usize.size := by
      simpa [Std.Usize.size, Std.Usize.numBits,
        UScalarTy.Usize_numBits_eq] using nodePos.hBounds
    have sizeLarge : 32 < Std.Usize.size := by
      rw [Std.Usize.size, Std.Usize.numBits,
        UScalarTy.Usize_numBits_eq]
      rcases System.Platform.numBits_eq with bits | bits <;>
        rw [bits] <;> norm_num
    apply Nat.mod_eq_of_lt
    by_contra wraps
    have atLeast : Std.Usize.size ≤ nodePos.val + 32 :=
      Nat.le_of_not_gt wraps
    have belowTwice : nodePos.val + 32 < 2 * Std.Usize.size := by omega
    have reduced : (nodePos.val + 32) % Std.Usize.size =
        nodePos.val + 32 - Std.Usize.size := by
      rw [Nat.mod_eq_sub_mod atLeast]
      exact Nat.mod_eq_of_lt (by omega)
    rw [reduced] at startLeEnd
    omega
  next bounds => simp at sliceRun

private theorem copied_sibling_is_reified_frontier
    (nodeBytes : Slice Std.U8) (nodePos : Std.Usize)
    (siblingSlice : Slice Std.U8) (sibling : GeneratedDigest)
    (frontier : List Digest32) (frontierOrdinal : Nat)
    (hflat : frontier.flatMap digestBytes =
      nodeBytes.val.map generatedU8ToByte)
    (cursorExact : nodePos.val = 32 * frontierOrdinal)
    (sliceRun : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) nodeBytes
      { start := nodePos,
        «end» := Std.Usize.wrapping_add nodePos 32#usize } =
      .ok siblingSlice)
    (copyRun : core.array.TryFromArrayCopySlice.try_from 32#usize
      core.marker.CopyU8 siblingSlice = .ok (.Ok sibling))
    (frontierBound : frontierOrdinal < frontier.length) :
    generatedArrayToDigest sibling = frontier[frontierOrdinal] := by
  apply digestBytes_injective
  rw [digestBytes_generatedArrayToDigest,
    copied_sibling_slice_exact nodeBytes nodePos siblingSlice sibling
      sliceRun copyRun,
    usize_add_32_exact_of_slice nodeBytes nodePos siblingSlice sliceRun,
    cursorExact]
  have exactSlice := reified_frontier_digest_slice_exact nodeBytes.val
    frontier hflat frontierOrdinal frontierBound
  rw [exactSlice]
  simp only [List.slice, Nat.mul_add]
  rw [← List.map_drop, ← List.map_take]

/-- Every released private tree has an odd binary depth, so the generated
even-root arm is unreachable once its selected depth is identified. -/
theorem released_binary_depth_is_odd
    (tree : V5PrivateSection) (generatedDepth : Std.U32)
    (depthExact : generatedDepth.val = binaryDepth tree) :
    ¬ generatedDepth &&& 1#u32 = 0#u32 := by
  intro even
  have evenValue := congrArg UScalar.val even
  simp only [UScalar.val_and] at evenValue
  cases tree <;> norm_num [binaryDepth] at depthExact evenValue
  all_goals omega

/-- The unchanged final-root witness, the exact constructed topology, and the
reified frontier bytes determine the complete model-level odd binary cap.
The only cursor premise is the number of 32-byte radix-frontier blocks already
consumed before the cap. -/
theorem final_root_witness_yields_binary_cap_data
    (sha256 : List ModelByte → Digest32)
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (binaryDepth : Std.U32) (level : GeneratedDigestVec)
    (nodePos : Std.Usize)
    (queries : Finset V5Query)
    (fields : FullExactConstructedTopologyFields queries topology)
    (oddParity : ¬ binaryDepth &&& 1#u32 = 0#u32)
    (frontier : List Digest32) (frontierOrdinal : Nat)
    (frontierFlat : frontier.flatMap digestBytes =
      nodeBytes.val.map generatedU8ToByte)
    (cursorExact : nodePos.val = 32 * frontierOrdinal)
    (witness : RawFinalRootWitness sha256 root nodeBytes topology
      binaryDepth level nodePos) :
    Nonempty (ExactOddBinaryCapData sha256 (generatedArrayToDigest root)
      (sharedLevelIndices queries 8)
      (level.val.map generatedArrayToDigest) frontier frontierOrdinal) := by
  have frontierLength := reified_frontier_length_exact nodeBytes.val frontier
    frontierFlat
  cases witness with
  | even indices levelSlice value indicesRun parity levelSliceRun
      indicesLength levelLength indexRun valueRun frontierConsumed rootEq =>
      exact False.elim (oddParity parity)
  | odd indices left right indicesRun parity location rootEq =>
      have topologyLevelLt : topology.radix_levels.val < 9 := by
        rw [fields.radixLevels]
        omega
      have plan := level_indices_follow_shared_plan queries topology
        topology.radix_levels indices fields topologyLevelLt indicesRun
      have planExact : indices.val.map (fun index => index.val) =
          sharedLevelIndices queries 8 := by
        simpa [fields.radixLevels] using plan
      cases location
      case both =>
          rename_i levelSlice levelSliceRun indicesLength levelLength
            leftIndexRun rightIndexRun frontierConsumed leftRun rightRun
          have sourceIndices := two_index_slice_exact indices 0#u32 1#u32
            indicesLength leftIndexRun rightIndexRun
          have activeExact : sharedLevelIndices queries 8 = [0, 1] := by
            rw [← planExact, sourceIndices]
            rfl
          have sourceLive := two_live_values_exact level levelSlice left
            right levelSliceRun levelLength leftRun rightRun
          have liveExact : level.val.map generatedArrayToDigest =
              [generatedArrayToDigest left,
                generatedArrayToDigest right] := by
            rw [sourceLive]
            rfl
          have cursorValue : nodePos.val = nodeBytes.val.length := by
            have raw := congrArg UScalar.val frontierConsumed
            simpa [Slice.len, Slice.length] using raw
          have consumedExact : frontierOrdinal = frontier.length := by
            rw [cursorExact, frontierLength] at cursorValue
            omega
          exact ⟨{
            left := generatedArrayToDigest left
            right := generatedArrayToDigest right
            location := ExactOddCapModelLocation.both _ _ activeExact
              liveExact consumedExact
            root_eq := rootEq }⟩
      case liveLeft =>
          rename_i levelSlice siblingSlice levelSliceRun indicesLength
            levelLength indexRun siblingSliceRun frontierConsumed valueRun
            siblingCopyRun
          have sourceIndices := one_index_slice_exact indices 0#u32
            indicesLength indexRun
          have activeExact : sharedLevelIndices queries 8 = [0] := by
            rw [← planExact, sourceIndices]
            rfl
          have sourceLive := one_live_value_exact level levelSlice left
            levelSliceRun levelLength valueRun
          have liveExact : level.val.map generatedArrayToDigest =
              [generatedArrayToDigest left] := by
            rw [sourceLive]
            rfl
          have addExact := usize_add_32_exact_of_slice nodeBytes nodePos
            siblingSlice siblingSliceRun
          have cursorValue : nodePos.val + 32 = nodeBytes.val.length := by
            have raw := congrArg UScalar.val frontierConsumed
            rw [addExact] at raw
            simpa [Slice.len, Slice.length] using raw
          have consumedExact : frontierOrdinal + 1 = frontier.length := by
            rw [cursorExact, frontierLength] at cursorValue
            omega
          have frontierBound : frontierOrdinal < frontier.length := by omega
          have siblingExact := copied_sibling_is_reified_frontier nodeBytes
            nodePos siblingSlice right frontier frontierOrdinal frontierFlat
            cursorExact siblingSliceRun siblingCopyRun frontierBound
          exact ⟨{
            left := generatedArrayToDigest left
            right := generatedArrayToDigest right
            location := ExactOddCapModelLocation.liveLeft _ _ activeExact
              liveExact frontierBound siblingExact consumedExact
            root_eq := rootEq }⟩
      case liveRight =>
          rename_i levelSlice siblingSlice levelSliceRun indicesLength
            levelLength indexRun siblingSliceRun frontierConsumed
            siblingCopyRun valueRun
          have sourceIndices := one_index_slice_exact indices 1#u32
            indicesLength indexRun
          have activeExact : sharedLevelIndices queries 8 = [1] := by
            rw [← planExact, sourceIndices]
            rfl
          have sourceLive := one_live_value_exact level levelSlice right
            levelSliceRun levelLength valueRun
          have liveExact : level.val.map generatedArrayToDigest =
              [generatedArrayToDigest right] := by
            rw [sourceLive]
            rfl
          have addExact := usize_add_32_exact_of_slice nodeBytes nodePos
            siblingSlice siblingSliceRun
          have cursorValue : nodePos.val + 32 = nodeBytes.val.length := by
            have raw := congrArg UScalar.val frontierConsumed
            rw [addExact] at raw
            simpa [Slice.len, Slice.length] using raw
          have consumedExact : frontierOrdinal + 1 = frontier.length := by
            rw [cursorExact, frontierLength] at cursorValue
            omega
          have frontierBound : frontierOrdinal < frontier.length := by omega
          have siblingExact := copied_sibling_is_reified_frontier nodeBytes
            nodePos siblingSlice left frontier frontierOrdinal frontierFlat
            cursorExact siblingSliceRun siblingCopyRun frontierBound
          exact ⟨{
            left := generatedArrayToDigest left
            right := generatedArrayToDigest right
            location := ExactOddCapModelLocation.liveRight _ _ activeExact
              liveExact frontierBound siblingExact consumedExact
            root_eq := rootEq }⟩

#print axioms released_binary_depth_is_odd
#print axioms final_root_witness_yields_binary_cap_data

end AspisV5MerkleUnchangedFullBinaryCapSemantics
