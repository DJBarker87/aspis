import V7MerkleK12LayoutBridge

open Aeneas Aeneas.Std Result

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Exact translated-path to frozen-opening bridge

This file is the semantic target for the compressed-frontier traversal proof.
`GeneratedSourcePath` is not a replacement verifier: every nonempty
constructor stores a successful call of the translated production
`node_hash_v7`, plus the position parity and parent-position facts selected by
that same translated branch.  The theorems below show that such a literal
source path is exactly the frozen bottom-up `foldPathAux` computation.
-/

namespace AspisV7MerkleK12AcceptedBridge


abbrev Byte := AspisPool.V7MerkleQueryGrammar.Byte
abbrev GeneratedHash := AspisV7MerkleK12SourceBridge.GeneratedHash
abbrev GeneratedDigest := Array Std.U8 26#usize

/-- The precise 208-bit function induced by the permitted SHA-256 callback
boundary.  Only the first 26 bytes are observed, matching production. -/
def frozenTruncate (sha256 : List Byte → List Byte) :
    AspisPool.V7MerkleQueryGrammar.RawHashInput → AspisPool.V7MerkleQueryGrammar.Digest208 :=
  fun input => AspisPool.V7MerkleQueryExtractor.fixedOfListD ((sha256 input).take 26)

theorem digestFixed_eq_frozenTruncate_of_bytes
    (sha256 : List Byte → List Byte) (input : AspisPool.V7MerkleQueryGrammar.RawHashInput)
    (output : GeneratedDigest)
    (bytesExact : AspisV7MerkleK12SourceBridge.generatedArrayBytes output =
      (sha256 input).take 26) :
    AspisV7MerkleK12LayoutBridge.digestFixed output = frozenTruncate sha256 input := by
  apply AspisPool.V7MerkleQueryGrammar.fixedBytes_injective
  rw [AspisV7MerkleK12LayoutBridge.fixedBytes_digestFixed]
  have exactLength : ((sha256 input).take 26).length = 26 := by
    rw [← bytesExact]
    exact AspisV7MerkleK12LayoutBridge.generatedArrayBytes_length output
  exact bytesExact.trans
    (AspisPool.V7MerkleQueryExtractor.fixedBytes_fixedOfListD_of_length _ exactLength).symm

theorem node_hash_v7_matches_frozen_digest
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256 sha256 hash)
    (left right output : GeneratedDigest)
    (run : V7MerkleK12Generated.v7_merkle208.node_hash_v7 hash left right = .ok output) :
    AspisV7MerkleK12LayoutBridge.digestFixed output = frozenTruncate sha256
      (AspisPool.V7MerkleQueryGrammar.serialize (.node (AspisV7MerkleK12LayoutBridge.digestFixed left)
        (AspisV7MerkleK12LayoutBridge.digestFixed right))) := by
  apply digestFixed_eq_frozenTruncate_of_bytes
  exact AspisV7MerkleK12LayoutBridge.node_hash_v7_matches_frozen_serialize sha256 hash hashSemantics
    left right output run

theorem c1_leaf_hash_v7_matches_frozen_digest
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256 sha256 hash)
    (value : Slice Std.U8) (salt : Array Std.U8 32#usize)
    (output : GeneratedDigest)
    (valueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes value).length = 403)
    (run : V7MerkleK12Generated.v7_merkle208.private_leaf_hash_v7
      hash 0x71#u8 value salt = .ok output) :
    AspisV7MerkleK12LayoutBridge.digestFixed output = frozenTruncate sha256
      (AspisPool.V7MerkleQueryGrammar.serialize (.c1Leaf (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 403) value)
        (AspisV7MerkleK12LayoutBridge.saltFixed salt))) := by
  apply digestFixed_eq_frozenTruncate_of_bytes
  exact AspisV7MerkleK12LayoutBridge.private_leaf_hash_v7_c1_matches_frozen_serialize
    sha256 hash hashSemantics value salt output valueLength run

theorem c2_leaf_hash_v7_matches_frozen_digest
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256 sha256 hash)
    (value : Slice Std.U8) (salt : Array Std.U8 32#usize)
    (output : GeneratedDigest)
    (valueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes value).length = 186)
    (run : V7MerkleK12Generated.v7_merkle208.private_leaf_hash_v7
      hash 0xf1#u8 value salt = .ok output) :
    AspisV7MerkleK12LayoutBridge.digestFixed output = frozenTruncate sha256
      (AspisPool.V7MerkleQueryGrammar.serialize (.c2Leaf (AspisV7MerkleK12LayoutBridge.sliceFixed (n := 186) value)
        (AspisV7MerkleK12LayoutBridge.saltFixed salt))) := by
  apply digestFixed_eq_frozenTruncate_of_bytes
  exact AspisV7MerkleK12LayoutBridge.private_leaf_hash_v7_c2_matches_frozen_serialize
    sha256 hash hashSemantics value salt output valueLength run

/-- One exact bottom-up authentication path through translated production
hash calls. `left` means the accumulated node was production's left child;
`right` means it was production's right child. -/
inductive GeneratedSourcePath (hash : GeneratedHash) :
    Nat → Std.U32 → GeneratedDigest → Std.U32 → GeneratedDigest → Type
  | zero (position : Std.U32) (digest : GeneratedDigest) :
      GeneratedSourcePath hash 0 position digest position digest
  | left {rounds : Nat} {position parentPosition rootPosition : Std.U32}
      {digest parent root : GeneratedDigest} (sibling : GeneratedDigest)
      (positionEven : position.val.testBit 0 = false)
      (parentPositionExact : parentPosition.val = position.val / 2)
      (hashRun : V7MerkleK12Generated.v7_merkle208.node_hash_v7
        hash digest sibling = .ok parent)
      (tail : GeneratedSourcePath hash rounds parentPosition parent
        rootPosition root) :
      GeneratedSourcePath hash (rounds + 1) position digest rootPosition root
  | right {rounds : Nat} {position parentPosition rootPosition : Std.U32}
      {digest parent root : GeneratedDigest} (sibling : GeneratedDigest)
      (positionOdd : position.val.testBit 0 = true)
      (parentPositionExact : parentPosition.val = position.val / 2)
      (hashRun : V7MerkleK12Generated.v7_merkle208.node_hash_v7
        hash sibling digest = .ok parent)
      (tail : GeneratedSourcePath hash rounds parentPosition parent
        rootPosition root) :
      GeneratedSourcePath hash (rounds + 1) position digest rootPosition root

def GeneratedSourcePath.siblingList
    {hash : GeneratedHash} {rounds : Nat}
    {position rootPosition : Std.U32} {digest root : GeneratedDigest} :
    GeneratedSourcePath hash rounds position digest rootPosition root →
      List AspisPool.V7MerkleQueryGrammar.Digest208
  | .zero _ _ => []
  | .left sibling _ _ _ tail =>
      AspisV7MerkleK12LayoutBridge.digestFixed sibling :: tail.siblingList
  | .right sibling _ _ _ tail =>
      AspisV7MerkleK12LayoutBridge.digestFixed sibling :: tail.siblingList

@[simp] theorem GeneratedSourcePath.siblingList_length
    {hash : GeneratedHash} {rounds : Nat}
    {position rootPosition : Std.U32} {digest root : GeneratedDigest}
    (path : GeneratedSourcePath hash rounds position digest rootPosition root) :
    path.siblingList.length = rounds := by
  induction path with
  | zero => rfl
  | left _ _ _ _ _ inductionHypothesis =>
      simp [GeneratedSourcePath.siblingList, inductionHypothesis]
  | right _ _ _ _ _ inductionHypothesis =>
      simp [GeneratedSourcePath.siblingList, inductionHypothesis]

def GeneratedSourcePath.siblingVector
    {hash : GeneratedHash} {rounds : Nat}
    {position rootPosition : Std.U32} {digest root : GeneratedDigest}
    (path : GeneratedSourcePath hash rounds position digest rootPosition root) :
    Fin rounds → AspisPool.V7MerkleQueryGrammar.Digest208 :=
  fun index => path.siblingList.getD index.val default

theorem GeneratedSourcePath.siblingVector_bytes
    {hash : GeneratedHash} {rounds : Nat}
    {position rootPosition : Std.U32} {digest root : GeneratedDigest}
    (path : GeneratedSourcePath hash rounds position digest rootPosition root) :
    List.ofFn path.siblingVector = path.siblingList := by
  have pointwise : path.siblingVector = fun index =>
      path.siblingList.get (Fin.cast path.siblingList_length.symm index) := by
    funext index
    exact List.getD_eq_get path.siblingList default
      (Fin.cast path.siblingList_length.symm index)
  rw [pointwise,
    ← List.ofFn_congr path.siblingList_length (List.get path.siblingList),
    List.ofFn_get]

/-- Structural source-to-model correspondence for one tree.  Every fold step
is justified by the exact translated node-hash call stored in the path. -/
theorem generated_source_path_foldPathAux
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256 sha256 hash)
    {rounds : Nat} {position rootPosition : Std.U32}
    {digest root : GeneratedDigest}
    (path : GeneratedSourcePath hash rounds position digest rootPosition root) :
    AspisPool.V7MerkleQueryExtractor.foldPathAux (frozenTruncate sha256) position.val
      (AspisV7MerkleK12LayoutBridge.digestFixed digest) path.siblingList =
        AspisV7MerkleK12LayoutBridge.digestFixed root := by
  induction path with
  | zero => rfl
  | left sibling positionEven parentPositionExact hashRun tail inductionHypothesis =>
      simp only [GeneratedSourcePath.siblingList, AspisPool.V7MerkleQueryExtractor.foldPathAux,
        positionEven, Bool.false_eq_true, ↓reduceIte]
      rw [← parentPositionExact]
      rw [← node_hash_v7_matches_frozen_digest sha256 hash hashSemantics
        _ _ _ hashRun]
      exact inductionHypothesis
  | right sibling positionOdd parentPositionExact hashRun tail inductionHypothesis =>
      simp only [GeneratedSourcePath.siblingList, AspisPool.V7MerkleQueryExtractor.foldPathAux,
        positionOdd, ↓reduceIte]
      rw [← parentPositionExact]
      rw [← node_hash_v7_matches_frozen_digest sha256 hash hashSemantics
        _ _ _ hashRun]
      exact inductionHypothesis

theorem generated_source_path_foldPath
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256 sha256 hash)
    {position rootPosition : Std.U32} {digest root : GeneratedDigest}
    (positionBound : position.val < 2 ^ AspisPool.V7MerkleQueryGrammar.treeDepth)
    (path : GeneratedSourcePath hash AspisPool.V7MerkleQueryGrammar.treeDepth position digest
      rootPosition root) :
    AspisPool.V7MerkleQueryExtractor.foldPath (frozenTruncate sha256)
      ⟨position.val, positionBound⟩ (AspisV7MerkleK12LayoutBridge.digestFixed digest)
      path.siblingVector = AspisV7MerkleK12LayoutBridge.digestFixed root := by
  unfold AspisPool.V7MerkleQueryExtractor.foldPath
  rw [show List.ofFn path.siblingVector = path.siblingList by
    exact path.siblingVector_bytes]
  exact generated_source_path_foldPathAux sha256 hash hashSemantics path

/-! ## Constructive compressed-frontier graph

`PairedHashEdge` is the small semantic unit exposed by one successful branch
of production's translated inner loop.  It records both tree hashes and the
single orientation selected by the public position.  `PairedHashRounds`
chains those exact edges across levels.  Its path projection below is wholly
constructive: sibling paths are outputs, never premises.
-/

def entryPosition (entry : AspisV7MerkleK12SourceBridge.GeneratedEntry) : Std.U32 := entry.1
def entryC1 (entry : AspisV7MerkleK12SourceBridge.GeneratedEntry) : GeneratedDigest := entry.2.1
def entryC2 (entry : AspisV7MerkleK12SourceBridge.GeneratedEntry) : GeneratedDigest := entry.2.2

inductive PairedHashEdge (hash : GeneratedHash) :
    AspisV7MerkleK12SourceBridge.GeneratedEntry → AspisV7MerkleK12SourceBridge.GeneratedEntry → Type
  | left {position parentPosition : Std.U32}
      {c1 c2 parentC1 parentC2 : GeneratedDigest}
      (c1Sibling c2Sibling : GeneratedDigest)
      (positionEven : position.val.testBit 0 = false)
      (parentPositionExact : parentPosition.val = position.val / 2)
      (c1HashRun : V7MerkleK12Generated.v7_merkle208.node_hash_v7
        hash c1 c1Sibling = .ok parentC1)
      (c2HashRun : V7MerkleK12Generated.v7_merkle208.node_hash_v7
        hash c2 c2Sibling = .ok parentC2) :
      PairedHashEdge hash (position, c1, c2)
        (parentPosition, parentC1, parentC2)
  | right {position parentPosition : Std.U32}
      {c1 c2 parentC1 parentC2 : GeneratedDigest}
      (c1Sibling c2Sibling : GeneratedDigest)
      (positionOdd : position.val.testBit 0 = true)
      (parentPositionExact : parentPosition.val = position.val / 2)
      (c1HashRun : V7MerkleK12Generated.v7_merkle208.node_hash_v7
        hash c1Sibling c1 = .ok parentC1)
      (c2HashRun : V7MerkleK12Generated.v7_merkle208.node_hash_v7
        hash c2Sibling c2 = .ok parentC2) :
      PairedHashEdge hash (position, c1, c2)
        (parentPosition, parentC1, parentC2)

structure PairedPathResult (hash : GeneratedHash) (rounds : Nat)
    (leaf : AspisV7MerkleK12SourceBridge.GeneratedEntry) (finalLevel : AspisV7MerkleK12SourceBridge.GeneratedLevel) where
  rootEntry : AspisV7MerkleK12SourceBridge.GeneratedEntry
  rootMember : rootEntry ∈ finalLevel.val
  c1Path : GeneratedSourcePath hash rounds (entryPosition leaf)
    (entryC1 leaf) (entryPosition rootEntry) (entryC1 rootEntry)
  c2Path : GeneratedSourcePath hash rounds (entryPosition leaf)
    (entryC2 leaf) (entryPosition rootEntry) (entryC2 rootEntry)

def PairedHashEdge.prependPaths
    {hash : GeneratedHash} {child parent : AspisV7MerkleK12SourceBridge.GeneratedEntry}
    (edge : PairedHashEdge hash child parent)
    {rounds : Nat} {finalLevel : AspisV7MerkleK12SourceBridge.GeneratedLevel}
    (tail : PairedPathResult hash rounds parent finalLevel) :
    PairedPathResult hash (rounds + 1) child finalLevel := by
  cases edge with
  | left c1Sibling c2Sibling positionEven parentPositionExact
      c1HashRun c2HashRun =>
      exact
        { rootEntry := tail.rootEntry
          rootMember := tail.rootMember
          c1Path := GeneratedSourcePath.left c1Sibling positionEven
            parentPositionExact c1HashRun tail.c1Path
          c2Path := GeneratedSourcePath.left c2Sibling positionEven
            parentPositionExact c2HashRun tail.c2Path }
  | right c1Sibling c2Sibling positionOdd parentPositionExact
      c1HashRun c2HashRun =>
      exact
        { rootEntry := tail.rootEntry
          rootMember := tail.rootMember
          c1Path := GeneratedSourcePath.right c1Sibling positionOdd
            parentPositionExact c1HashRun tail.c1Path
          c2Path := GeneratedSourcePath.right c2Sibling positionOdd
            parentPositionExact c2HashRun tail.c2Path }

/-- One complete translated sparse-frontier round.  Every live child is sent
to an actual pushed parent by the exact paired node-hash branch that created
that parent. -/
structure PairedHashRound (hash : GeneratedHash)
    (level next : AspisV7MerkleK12SourceBridge.GeneratedLevel) where
  parentOf : ∀ child, child ∈ level.val → AspisV7MerkleK12SourceBridge.GeneratedEntry
  parentMember : ∀ child member, parentOf child member ∈ next.val
  edge : ∀ child member, PairedHashEdge hash child (parentOf child member)

inductive PairedHashRounds (hash : GeneratedHash) :
    Nat → AspisV7MerkleK12SourceBridge.GeneratedLevel → AspisV7MerkleK12SourceBridge.GeneratedLevel → Type
  | zero (level : AspisV7MerkleK12SourceBridge.GeneratedLevel) : PairedHashRounds hash 0 level level
  | step {rounds : Nat} {level next finalLevel : AspisV7MerkleK12SourceBridge.GeneratedLevel}
      (head : PairedHashRound hash level next)
      (tail : PairedHashRounds hash rounds next finalLevel) :
      PairedHashRounds hash (rounds + 1) level finalLevel

noncomputable def PairedHashRounds.pathsFromMember
    {hash : GeneratedHash} {rounds : Nat}
    {level finalLevel : AspisV7MerkleK12SourceBridge.GeneratedLevel}
    (trace : PairedHashRounds hash rounds level finalLevel)
    (child : AspisV7MerkleK12SourceBridge.GeneratedEntry) (member : child ∈ level.val) :
    PairedPathResult hash rounds child finalLevel := by
  induction trace generalizing child with
  | zero =>
      exact
        { rootEntry := child
          rootMember := member
          c1Path := GeneratedSourcePath.zero _ _
          c2Path := GeneratedSourcePath.zero _ _ }
  | @step remaining current next final head tail inductionHypothesis =>
      let parent := head.parentOf child member
      let parentMember := head.parentMember child member
      exact (head.edge child member).prependPaths
        (inductionHypothesis parent parentMember)

/-- The frozen paired opening determined by two exact source paths and the
single production record salt used by both leaf hash calls. -/
def openingOfSourcePaths
    {hash : GeneratedHash} {position rootPosition : Std.U32}
    {c1Leaf c2Leaf c1Root c2Root : GeneratedDigest}
    (positionBound : position.val < 2 ^ AspisPool.V7MerkleQueryGrammar.treeDepth)
    (c1Value c2Value : Slice Std.U8) (salt : Array Std.U8 32#usize)
    (c1Path : GeneratedSourcePath hash AspisPool.V7MerkleQueryGrammar.treeDepth position c1Leaf
      rootPosition c1Root)
    (c2Path : GeneratedSourcePath hash AspisPool.V7MerkleQueryGrammar.treeDepth position c2Leaf
      rootPosition c2Root) : AspisPool.V7MerkleQueryExtractor.PairedOpening where
  position := ⟨position.val, positionBound⟩
  c1Value := AspisV7MerkleK12LayoutBridge.sliceFixed (n := 403) c1Value
  c2Value := AspisV7MerkleK12LayoutBridge.sliceFixed (n := 186) c2Value
  sharedSalt := AspisV7MerkleK12LayoutBridge.saltFixed salt
  c1Siblings := c1Path.siblingVector
  c2Siblings := c2Path.siblingVector

theorem openingOfSourcePaths_authenticates
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256 sha256 hash)
    {position rootPosition : Std.U32}
    {c1Leaf c2Leaf c1Root c2Root : GeneratedDigest}
    (positionBound : position.val < 2 ^ AspisPool.V7MerkleQueryGrammar.treeDepth)
    (c1Value c2Value : Slice Std.U8) (salt : Array Std.U8 32#usize)
    (c1Length : (AspisV7MerkleK12SourceBridge.generatedSliceBytes c1Value).length = 403)
    (c2Length : (AspisV7MerkleK12SourceBridge.generatedSliceBytes c2Value).length = 186)
    (c1LeafRun : V7MerkleK12Generated.v7_merkle208.private_leaf_hash_v7
      hash 0x71#u8 c1Value salt = .ok c1Leaf)
    (c2LeafRun : V7MerkleK12Generated.v7_merkle208.private_leaf_hash_v7
      hash 0xf1#u8 c2Value salt = .ok c2Leaf)
    (c1Path : GeneratedSourcePath hash AspisPool.V7MerkleQueryGrammar.treeDepth position c1Leaf
      rootPosition c1Root)
    (c2Path : GeneratedSourcePath hash AspisPool.V7MerkleQueryGrammar.treeDepth position c2Leaf
      rootPosition c2Root) :
    let opening := openingOfSourcePaths positionBound c1Value c2Value salt
      c1Path c2Path
    AspisPool.V7MerkleQueryExtractor.foldPath (frozenTruncate sha256) opening.position
        (AspisPool.V7MerkleQueryExtractor.c1DisclosedLeafDigest (frozenTruncate sha256) opening)
        opening.c1Siblings = AspisV7MerkleK12LayoutBridge.digestFixed c1Root ∧
      AspisPool.V7MerkleQueryExtractor.foldPath (frozenTruncate sha256) opening.position
        (AspisPool.V7MerkleQueryExtractor.c2DisclosedLeafDigest (frozenTruncate sha256) opening)
        opening.c2Siblings = AspisV7MerkleK12LayoutBridge.digestFixed c2Root := by
  dsimp only [openingOfSourcePaths, AspisPool.V7MerkleQueryExtractor.c1DisclosedLeafDigest,
    AspisPool.V7MerkleQueryExtractor.c2DisclosedLeafDigest]
  constructor
  · rw [← c1_leaf_hash_v7_matches_frozen_digest sha256 hash hashSemantics
      c1Value salt c1Leaf c1Length c1LeafRun]
    exact generated_source_path_foldPath sha256 hash hashSemantics
      positionBound c1Path
  · rw [← c2_leaf_hash_v7_matches_frozen_digest sha256 hash hashSemantics
      c2Value salt c2Leaf c2Length c2LeafRun]
    exact generated_source_path_foldPath sha256 hash hashSemantics
      positionBound c2Path

/-! ## Exact sixteen-opening package

The fields below are deliberately source-facing.  Leaf fields are successful
calls of the two translated production leaf-hash branches.  Path fields are
chains of successful translated production node-hash calls, not equations of
the frozen acceptance predicate.  A later sparse-frontier trace theorem can
therefore construct this package without assuming authentication.
-/

structure PairedSourceSeed (hash : GeneratedHash) where
  position : Std.U32
  positionBound : position.val < 2 ^ AspisPool.V7MerkleQueryGrammar.treeDepth
  c1Value : Slice Std.U8
  c2Value : Slice Std.U8
  salt : Array Std.U8 32#usize
  c1ValueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes c1Value).length = 403
  c2ValueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes c2Value).length = 186
  c1Leaf : GeneratedDigest
  c2Leaf : GeneratedDigest
  c1LeafRun : V7MerkleK12Generated.v7_merkle208.private_leaf_hash_v7
    hash 0x71#u8 c1Value salt = .ok c1Leaf
  c2LeafRun : V7MerkleK12Generated.v7_merkle208.private_leaf_hash_v7
    hash 0xf1#u8 c2Value salt = .ok c2Leaf

def PairedSourceSeed.entry
    {hash : GeneratedHash} (seed : PairedSourceSeed hash) :
    AspisV7MerkleK12SourceBridge.GeneratedEntry :=
  (seed.position, seed.c1Leaf, seed.c2Leaf)

def PairedSourceSeed.finitePosition
    {hash : GeneratedHash} (seed : PairedSourceSeed hash) :
    AspisPool.V7MerkleQueryExtractor.Position :=
  ⟨seed.position.val, seed.positionBound⟩

structure PairedSourceOpening
    (hash : GeneratedHash) (c1Root c2Root : GeneratedDigest) where
  position : Std.U32
  positionBound : position.val < 2 ^ AspisPool.V7MerkleQueryGrammar.treeDepth
  c1Value : Slice Std.U8
  c2Value : Slice Std.U8
  salt : Array Std.U8 32#usize
  c1ValueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes c1Value).length = 403
  c2ValueLength : (AspisV7MerkleK12SourceBridge.generatedSliceBytes c2Value).length = 186
  c1Leaf : GeneratedDigest
  c2Leaf : GeneratedDigest
  c1LeafRun : V7MerkleK12Generated.v7_merkle208.private_leaf_hash_v7
    hash 0x71#u8 c1Value salt = .ok c1Leaf
  c2LeafRun : V7MerkleK12Generated.v7_merkle208.private_leaf_hash_v7
    hash 0xf1#u8 c2Value salt = .ok c2Leaf
  c1Path : GeneratedSourcePath hash AspisPool.V7MerkleQueryGrammar.treeDepth position c1Leaf
    0#u32 c1Root
  c2Path : GeneratedSourcePath hash AspisPool.V7MerkleQueryGrammar.treeDepth position c2Leaf
    0#u32 c2Root

def sourceOpeningOfSeedAndPaths
    {hash : GeneratedHash} {c1Root c2Root : GeneratedDigest}
    {finalLevel : AspisV7MerkleK12SourceBridge.GeneratedLevel}
    (seed : PairedSourceSeed hash)
    (paths : PairedPathResult hash AspisPool.V7MerkleQueryGrammar.treeDepth seed.entry finalLevel)
    (rootExact : paths.rootEntry = (0#u32, c1Root, c2Root)) :
    PairedSourceOpening hash c1Root c2Root := by
  rcases paths with ⟨rootEntry, rootMember, c1Path, c2Path⟩
  dsimp only at rootExact
  subst rootEntry
  exact
    { position := seed.position
      positionBound := seed.positionBound
      c1Value := seed.c1Value
      c2Value := seed.c2Value
      salt := seed.salt
      c1ValueLength := seed.c1ValueLength
      c2ValueLength := seed.c2ValueLength
      c1Leaf := seed.c1Leaf
      c2Leaf := seed.c2Leaf
      c1LeafRun := seed.c1LeafRun
      c2LeafRun := seed.c2LeafRun
      c1Path := by
        simpa [PairedSourceSeed.entry, entryPosition, entryC1] using c1Path
      c2Path := by
        simpa [PairedSourceSeed.entry, entryPosition, entryC2] using c2Path }

def PairedSourceOpening.finitePosition
    {hash : GeneratedHash} {c1Root c2Root : GeneratedDigest}
    (opening : PairedSourceOpening hash c1Root c2Root) : AspisPool.V7MerkleQueryExtractor.Position :=
  ⟨opening.position.val, opening.positionBound⟩

def PairedSourceOpening.toFrozenOpening
    {hash : GeneratedHash} {c1Root c2Root : GeneratedDigest}
    (opening : PairedSourceOpening hash c1Root c2Root) :
    AspisPool.V7MerkleQueryExtractor.PairedOpening :=
  openingOfSourcePaths opening.positionBound opening.c1Value opening.c2Value
    opening.salt opening.c1Path opening.c2Path

theorem PairedSourceOpening.authenticates
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256 sha256 hash)
    (c1Root c2Root : GeneratedDigest)
    (opening : PairedSourceOpening hash c1Root c2Root) :
    AspisPool.V7MerkleQueryExtractor.foldPath (frozenTruncate sha256)
        opening.toFrozenOpening.position
        (AspisPool.V7MerkleQueryExtractor.c1DisclosedLeafDigest (frozenTruncate sha256)
          opening.toFrozenOpening)
        opening.toFrozenOpening.c1Siblings = AspisV7MerkleK12LayoutBridge.digestFixed c1Root ∧
      AspisPool.V7MerkleQueryExtractor.foldPath (frozenTruncate sha256)
        opening.toFrozenOpening.position
        (AspisPool.V7MerkleQueryExtractor.c2DisclosedLeafDigest (frozenTruncate sha256)
          opening.toFrozenOpening)
        opening.toFrozenOpening.c2Siblings = AspisV7MerkleK12LayoutBridge.digestFixed c2Root := by
  exact openingOfSourcePaths_authenticates sha256 hash hashSemantics
    opening.positionBound opening.c1Value opening.c2Value opening.salt
    opening.c1ValueLength opening.c2ValueLength opening.c1LeafRun
    opening.c2LeafRun opening.c1Path opening.c2Path

abbrev PairedSourceOpeningBatch
    (hash : GeneratedHash) (c1Root c2Root : GeneratedDigest) :=
  Fin AspisPool.V7MerkleQueryGrammar.disclosedQueryPairs → PairedSourceOpening hash c1Root c2Root

def proofOfSourceOpeningBatch
    {hash : GeneratedHash} {c1Root c2Root : GeneratedDigest}
    (batch : PairedSourceOpeningBatch hash c1Root c2Root) :
    AspisPool.V7MerkleQueryExtractor.TwoTreeOpeningProof :=
  fun ordinal => (batch ordinal).toFrozenOpening

def rootsOfGeneratedDigests (c1Root c2Root : GeneratedDigest) :
    AspisPool.V7MerkleQueryExtractor.Roots where
  c1 := AspisV7MerkleK12LayoutBridge.digestFixed c1Root
  c2 := AspisV7MerkleK12LayoutBridge.digestFixed c2Root

abbrev PairedSourceSeedBatch (hash : GeneratedHash) :=
  Fin AspisPool.V7MerkleQueryGrammar.disclosedQueryPairs → PairedSourceSeed hash

/-- Deterministically project sixteen frozen opening records from the exact
translated hash graph. -/
noncomputable def sourceOpeningBatchOfRounds
    {hash : GeneratedHash} {c1Root c2Root : GeneratedDigest}
    (seeds : PairedSourceSeedBatch hash)
    (initialLevel finalLevel : AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (rounds : PairedHashRounds hash AspisPool.V7MerkleQueryGrammar.treeDepth initialLevel finalLevel)
    (initialEntriesExact : initialLevel.val =
      List.ofFn (fun ordinal => (seeds ordinal).entry))
    (finalSingletonExact : finalLevel.val = [(0#u32, c1Root, c2Root)]) :
    PairedSourceOpeningBatch hash c1Root c2Root :=
  fun ordinal => by
    have seedMember : (seeds ordinal).entry ∈ initialLevel.val := by
      rw [initialEntriesExact]
      simp only [List.mem_ofFn]
      exact ⟨ordinal, rfl⟩
    let paths := rounds.pathsFromMember (seeds ordinal).entry seedMember
    have rootExact : paths.rootEntry = (0#u32, c1Root, c2Root) := by
      have rootMember := paths.rootMember
      rw [finalSingletonExact] at rootMember
      simpa only [List.mem_singleton] using rootMember
    exact sourceOpeningOfSeedAndPaths (seeds ordinal) paths rootExact

@[simp] theorem sourceOpeningOfSeedAndPaths_finitePosition
    {hash : GeneratedHash} {c1Root c2Root : GeneratedDigest}
    {finalLevel : AspisV7MerkleK12SourceBridge.GeneratedLevel}
    (seed : PairedSourceSeed hash)
    (paths : PairedPathResult hash AspisPool.V7MerkleQueryGrammar.treeDepth seed.entry finalLevel)
    (rootExact : paths.rootEntry = (0#u32, c1Root, c2Root)) :
    (sourceOpeningOfSeedAndPaths seed paths rootExact).finitePosition =
      seed.finitePosition := by
  rcases paths with ⟨rootEntry, rootMember, c1Path, c2Path⟩
  dsimp only at rootExact
  subst rootEntry
  rfl

theorem sourceOpeningBatchOfRounds_finitePosition
    {hash : GeneratedHash} {c1Root c2Root : GeneratedDigest}
    (seeds : PairedSourceSeedBatch hash)
    (initialLevel finalLevel : AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (rounds : PairedHashRounds hash AspisPool.V7MerkleQueryGrammar.treeDepth initialLevel finalLevel)
    (initialEntriesExact : initialLevel.val =
      List.ofFn (fun ordinal => (seeds ordinal).entry))
    (finalSingletonExact : finalLevel.val = [(0#u32, c1Root, c2Root)])
    (ordinal : Fin AspisPool.V7MerkleQueryGrammar.disclosedQueryPairs) :
    (sourceOpeningBatchOfRounds seeds initialLevel finalLevel rounds
      initialEntriesExact finalSingletonExact ordinal).finitePosition =
        (seeds ordinal).finitePosition := by
  unfold sourceOpeningBatchOfRounds
  dsimp only
  apply sourceOpeningOfSeedAndPaths_finitePosition

/-- Sixteen exact source opening records, with the caller's no-duplicate
position fact, satisfy the frozen accepted-opening predicate literally.  The
proof unfolds the frozen predicate; it does not assume a root/path acceptance
equation. -/
theorem exact_source_opening_batch_accepted
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256 sha256 hash)
    (c1Root c2Root : GeneratedDigest)
    (batch : PairedSourceOpeningBatch hash c1Root c2Root)
    (positionsInjective : Function.Injective
      (fun ordinal => (batch ordinal).finitePosition)) :
    AspisPool.V7MerkleQueryExtractor.accepted_two_tree_openings (frozenTruncate sha256)
      (rootsOfGeneratedDigests c1Root c2Root)
      (proofOfSourceOpeningBatch batch) := by
  constructor
  · have positionsNodup :
        (List.ofFn (fun ordinal => (batch ordinal).finitePosition)).Nodup :=
      List.nodup_ofFn.mpr positionsInjective
    change (List.ofFn (fun ordinal =>
      (proofOfSourceOpeningBatch batch ordinal).position)).Nodup
    simpa [proofOfSourceOpeningBatch, PairedSourceOpening.toFrozenOpening,
      openingOfSourcePaths, PairedSourceOpening.finitePosition] using
        positionsNodup
  · intro ordinal
    exact (batch ordinal).authenticates sha256 hash hashSemantics
      c1Root c2Root

/-- Constructive compressed-frontier adapter.  Exactly eighteen paired hash
rounds over exactly sixteen caller seeds produce a frozen proof accepted at
the two production roots.  The paths in the conclusion are computed by
`PairedHashRounds.pathsFromMember`; no path or root-authentication premise is
present. -/
theorem exact_source_hash_rounds_imply_accepted_two_tree_openings
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256 sha256 hash)
    (c1Root c2Root : GeneratedDigest)
    (seeds : PairedSourceSeedBatch hash)
    (initialLevel finalLevel : AspisV7MerkleK12SourceBridge.GeneratedLevel)
    (rounds : PairedHashRounds hash AspisPool.V7MerkleQueryGrammar.treeDepth initialLevel finalLevel)
    (initialEntriesExact : initialLevel.val =
      List.ofFn (fun ordinal => (seeds ordinal).entry))
    (finalSingletonExact : finalLevel.val = [(0#u32, c1Root, c2Root)])
    (positionsInjective : Function.Injective
      (fun ordinal => (seeds ordinal).finitePosition)) :
    AspisPool.V7MerkleQueryExtractor.accepted_two_tree_openings (frozenTruncate sha256)
      (rootsOfGeneratedDigests c1Root c2Root)
      (proofOfSourceOpeningBatch
        (sourceOpeningBatchOfRounds seeds initialLevel finalLevel rounds
          initialEntriesExact finalSingletonExact)) := by
  apply exact_source_opening_batch_accepted sha256 hash hashSemantics
  intro left right equal
  apply positionsInjective
  change (seeds left).finitePosition = (seeds right).finitePosition
  rw [← sourceOpeningBatchOfRounds_finitePosition seeds initialLevel
      finalLevel rounds initialEntriesExact finalSingletonExact left,
    ← sourceOpeningBatchOfRounds_finitePosition seeds initialLevel
      finalLevel rounds initialEntriesExact finalSingletonExact right]
  exact equal

#print axioms digestFixed_eq_frozenTruncate_of_bytes
#print axioms node_hash_v7_matches_frozen_digest
#print axioms c1_leaf_hash_v7_matches_frozen_digest
#print axioms c2_leaf_hash_v7_matches_frozen_digest
#print axioms GeneratedSourcePath.siblingList_length
#print axioms GeneratedSourcePath.siblingVector_bytes
#print axioms generated_source_path_foldPathAux
#print axioms generated_source_path_foldPath
#print axioms openingOfSourcePaths_authenticates
#print axioms PairedSourceOpening.authenticates
#print axioms exact_source_opening_batch_accepted
#print axioms PairedHashRounds.pathsFromMember
#print axioms exact_source_hash_rounds_imply_accepted_two_tree_openings

end AspisV7MerkleK12AcceptedBridge
