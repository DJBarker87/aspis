import AspisFormal.Pool.V7MerkleExtractedSubtreeCommitment
import AspisFormal.Pool.V7MerkleOpeningBinding

/-!
# Canonical openings of independently committed V7 words

This module turns a successful independent `commitTree` computation into a
perfect binary tree.  The perfect-tree representation is the source of the
canonical same-position opening compared with the verifier-supplied opening
by the K1.2 binding reduction.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisPool.V7MerkleCanonicalOpening

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleExtractedSubtreeCommitment
open AspisPool.V7MerkleOpeningBinding

universe u

inductive PerfectTree (Leaf : Type u) : Nat → Type u where
  | leaf (value : Leaf) : PerfectTree Leaf 0
  | node {height : Nat}
      (left right : PerfectTree Leaf height) : PerfectTree Leaf (height + 1)

def PerfectTree.leaves {Leaf : Type u} :
    {height : Nat} → PerfectTree Leaf height → List Leaf
  | 0, .leaf value => [value]
  | _ + 1, .node left right => left.leaves ++ right.leaves

def PerfectTree.root {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafDigest : Leaf → Digest208) :
    {height : Nat} → PerfectTree Leaf height → Digest208
  | 0, .leaf value => leafDigest value
  | _ + 1, .node left right =>
      nodeDigest truncateSha256
        (left.root truncateSha256 leafDigest)
        (right.root truncateSha256 leafDigest)

theorem PerfectTree.leaves_length {Leaf : Type u} :
    ∀ {height : Nat} (tree : PerfectTree Leaf height),
      tree.leaves.length = 2 ^ height := by
  intro height tree
  induction tree with
  | leaf value => simp [PerfectTree.leaves]
  | node left right leftInduction rightInduction =>
      simp [PerfectTree.leaves, leftInduction, rightInduction, pow_succ]
      omega

theorem PerfectTree.commit_leaves {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafDigest : Leaf → Digest208) :
    ∀ {height : Nat} (tree : PerfectTree Leaf height),
      commitTree truncateSha256 leafDigest height tree.leaves =
        some (tree.root truncateSha256 leafDigest) := by
  intro height tree
  induction tree with
  | leaf value => simp [PerfectTree.leaves, PerfectTree.root, commitTree]
  | @node height left right leftInduction rightInduction =>
      have leftLength := left.leaves_length
      have rightLength := right.leaves_length
      have totalLength :
          (left.leaves ++ right.leaves).length = 2 ^ (height + 1) := by
        simp [leftLength, rightLength, pow_succ]
        omega
      simp [PerfectTree.leaves, PerfectTree.root, commitTree, totalLength,
        leftLength, rightLength, leftInduction, rightInduction]

theorem commitTree_success_yields_perfect_tree {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafDigest : Leaf → Digest208) : ∀
    (height : Nat) (leaves : List Leaf) (root : Digest208),
    commitTree truncateSha256 leafDigest height leaves = some root →
      ∃ tree : PerfectTree Leaf height,
        tree.leaves = leaves ∧
          tree.root truncateSha256 leafDigest = root := by
  intro height
  induction height with
  | zero =>
      intro leaves root success
      cases leaves with
      | nil => simp [commitTree] at success
      | cons leaf rest =>
          cases rest with
          | nil =>
              simp [commitTree] at success
              subst root
              exact ⟨.leaf leaf, rfl, rfl⟩
          | cons next rest => simp [commitTree] at success
  | succ height inductionHypothesis =>
      intro leaves root success
      by_cases lengthExact : leaves.length = 2 ^ (height + 1)
      · cases leftEquation : commitTree truncateSha256 leafDigest height
            (leaves.take (2 ^ height)) with
        | none =>
            simp [commitTree, lengthExact, leftEquation] at success
        | some leftRoot =>
            cases rightEquation : commitTree truncateSha256 leafDigest height
                (leaves.drop (2 ^ height)) with
            | none =>
                simp [commitTree, lengthExact, leftEquation, rightEquation]
                  at success
            | some rightRoot =>
                have rootExact :
                    nodeDigest truncateSha256 leftRoot rightRoot = root := by
                  simpa [commitTree, lengthExact, leftEquation, rightEquation]
                    using success
                obtain ⟨leftTree, leftLeaves, leftTreeRoot⟩ :=
                  inductionHypothesis (leaves.take (2 ^ height)) leftRoot
                    leftEquation
                obtain ⟨rightTree, rightLeaves, rightTreeRoot⟩ :=
                  inductionHypothesis (leaves.drop (2 ^ height)) rightRoot
                    rightEquation
                refine ⟨.node leftTree rightTree, ?_, ?_⟩
                · simp [PerfectTree.leaves, leftLeaves, rightLeaves]
                · simp [PerfectTree.root, leftTreeRoot, rightTreeRoot, rootExact]
      · simp [commitTree, lengthExact] at success

/-! ## Canonical same-position authentication paths -/

def PerfectTree.openingAt {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafDigest : Leaf → Digest208) :
    {height : Nat} → PerfectTree Leaf height → Nat → Leaf × List Digest208
  | 0, .leaf value, _ => (value, [])
  | height + 1, .node left right, position =>
      if position.testBit height then
        let child := right.openingAt truncateSha256 leafDigest position
        (child.1,
          child.2 ++ [left.root truncateSha256 leafDigest])
      else
        let child := left.openingAt truncateSha256 leafDigest position
        (child.1,
          child.2 ++ [right.root truncateSha256 leafDigest])

theorem PerfectTree.openingAt_siblings_length {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafDigest : Leaf → Digest208) :
    ∀ {height : Nat} (tree : PerfectTree Leaf height) (position : Nat),
      (tree.openingAt truncateSha256 leafDigest position).2.length = height := by
  intro height tree
  induction tree with
  | leaf value => intro position; simp [PerfectTree.openingAt]
  | @node height left right leftInduction rightInduction =>
      intro position
      by_cases direction : position.testBit height
      · simp [PerfectTree.openingAt, direction, rightInduction]
      · simp [PerfectTree.openingAt, direction, leftInduction]

theorem foldPathAux_append
    (truncateSha256 : RawHashInput → Digest208) : ∀
    (initialPath remainingPath : List Digest208)
      (position : Nat) (current : Digest208),
    foldPathAux truncateSha256 position current
        (initialPath ++ remainingPath) =
      foldPathAux truncateSha256 (position / 2 ^ initialPath.length)
        (foldPathAux truncateSha256 position current initialPath)
        remainingPath := by
  intro initialPath
  induction initialPath with
  | nil =>
      intro remainingPath position current
      simp [foldPathAux]
  | cons sibling rest inductionHypothesis =>
      intro remainingPath position current
      rw [List.cons_append, foldPathAux_cons]
      rw [inductionHypothesis]
      rw [foldPathAux_cons]
      have positionExact :
          position / 2 / 2 ^ rest.length =
            position / 2 ^ (rest.length + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ,
          Nat.mul_comm 2 (2 ^ rest.length)]
      rw [positionExact]
      simp only [List.length_cons]

theorem PerfectTree.openingAt_authenticates {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafDigest : Leaf → Digest208) :
    ∀ {height : Nat} (tree : PerfectTree Leaf height) (position : Nat),
      foldPathAux truncateSha256 position
          (leafDigest (tree.openingAt truncateSha256 leafDigest position).1)
          (tree.openingAt truncateSha256 leafDigest position).2 =
        tree.root truncateSha256 leafDigest := by
  intro height tree
  induction tree with
  | leaf value =>
      intro position
      simp [PerfectTree.openingAt, PerfectTree.root, foldPathAux]
  | @node height left right leftInduction rightInduction =>
      intro position
      by_cases direction : position.testBit height
      · simp [PerfectTree.openingAt, direction, PerfectTree.root]
        rw [foldPathAux_append]
        rw [rightInduction]
        rw [right.openingAt_siblings_length]
        have topDirection :
            (position / 2 ^ height).testBit 0 = true := by
          rw [Nat.testBit_div_two_pow]
          simpa using direction
        simp [foldPathAux, topDirection, nodeDigest]
      · have directionFalse : position.testBit height = false :=
          Bool.eq_false_iff.mpr direction
        simp [PerfectTree.openingAt, directionFalse, PerfectTree.root]
        rw [foldPathAux_append]
        rw [leftInduction]
        rw [left.openingAt_siblings_length]
        have topDirection :
            (position / 2 ^ height).testBit 0 = false := by
          rw [Nat.testBit_div_two_pow]
          simpa using directionFalse
        simp [foldPathAux, topDirection, nodeDigest]

theorem PerfectTree.openingAt_eq_of_low_bits_eq {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafDigest : Leaf → Digest208) :
    ∀ {height : Nat} (tree : PerfectTree Leaf height)
      (leftPosition rightPosition : Nat),
      (∀ bit, bit < height →
        leftPosition.testBit bit = rightPosition.testBit bit) →
      tree.openingAt truncateSha256 leafDigest leftPosition =
        tree.openingAt truncateSha256 leafDigest rightPosition := by
  intro height tree
  induction tree with
  | leaf value =>
      intro leftPosition rightPosition _sameBits
      rfl
  | @node height left right leftInduction rightInduction =>
      intro leftPosition rightPosition sameBits
      have topBit := sameBits height (by omega)
      have lowerBits : ∀ bit, bit < height →
          leftPosition.testBit bit = rightPosition.testBit bit := by
        intro bit bitLt
        exact sameBits bit (by omega)
      by_cases leftDirection : leftPosition.testBit height
      · have rightDirection : rightPosition.testBit height = true := by
          rw [← topBit]
          exact leftDirection
        simp [PerfectTree.openingAt, leftDirection, rightDirection,
          rightInduction leftPosition rightPosition lowerBits]
      · have leftDirectionFalse : leftPosition.testBit height = false :=
          Bool.eq_false_iff.mpr leftDirection
        have rightDirectionFalse : rightPosition.testBit height = false := by
          rw [← topBit]
          exact leftDirectionFalse
        simp [PerfectTree.openingAt, leftDirectionFalse, rightDirectionFalse,
          leftInduction leftPosition rightPosition lowerBits]

theorem PerfectTree.openingAt_leaf_is_getElem {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafDigest : Leaf → Digest208) :
    ∀ {height : Nat} (tree : PerfectTree Leaf height) (position : Nat),
      position < 2 ^ height →
      tree.leaves[position]? =
        some (tree.openingAt truncateSha256 leafDigest position).1 := by
  intro height tree
  induction tree with
  | leaf value =>
      intro position positionBound
      have positionZero : position = 0 := by omega
      subst position
      simp [PerfectTree.leaves, PerfectTree.openingAt]
  | @node height left right leftInduction rightInduction =>
      intro position positionBound
      have leftLength : left.leaves.length = 2 ^ height :=
        left.leaves_length
      by_cases direction : position.testBit height
      · have rightHalf : 2 ^ height ≤ position :=
          Nat.ge_two_pow_of_testBit direction
        let relativePosition := position - 2 ^ height
        have relativeBound : relativePosition < 2 ^ height := by
          dsimp [relativePosition]
          rw [pow_succ] at positionBound
          omega
        have lowBits : ∀ bit, bit < height →
            position.testBit bit = relativePosition.testBit bit := by
          intro bit bitLt
          have decomposition :
              2 ^ height * 1 + relativePosition = position := by
            dsimp [relativePosition]
            omega
          have bitEquation :=
            Nat.testBit_two_pow_mul_add 1 relativeBound bit
          rw [decomposition] at bitEquation
          simpa [bitLt] using bitEquation
        have openingEqual := right.openingAt_eq_of_low_bits_eq
          truncateSha256 leafDigest position relativePosition lowBits
        rw [PerfectTree.leaves, List.getElem?_append_right]
        · simpa [PerfectTree.openingAt, direction, openingEqual, leftLength,
            relativePosition] using
              rightInduction relativePosition relativeBound
        · simpa [leftLength] using rightHalf
      · have directionFalse : position.testBit height = false :=
          Bool.eq_false_iff.mpr direction
        have leftHalf : position < 2 ^ height := by
          by_contra notLeft
          have topTrue :=
            Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
              (Nat.le_of_not_gt notLeft) positionBound
          exact direction (by simpa using topTrue)
        rw [PerfectTree.leaves, List.getElem?_append_left]
        · simpa [PerfectTree.openingAt, directionFalse] using
            leftInduction position leftHalf
        · simpa [leftLength] using leftHalf

def siblingPathOfList {height : Nat} (siblings : List Digest208)
    (lengthExact : siblings.length = height) : Fin height → Digest208 :=
  fun index => siblings.get (Fin.cast lengthExact.symm index)

theorem ofFn_siblingPathOfList {height : Nat}
    (siblings : List Digest208) (lengthExact : siblings.length = height) :
    List.ofFn (siblingPathOfList siblings lengthExact) = siblings := by
  change List.ofFn (fun index : Fin height =>
    siblings.get (Fin.cast lengthExact.symm index)) = siblings
  rw [← List.ofFn_congr lengthExact siblings.get]
  exact List.ofFn_get siblings

def PerfectTree.canonicalSiblingPath {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafDigest : Leaf → Digest208)
    (tree : PerfectTree Leaf treeDepth) (position : Position) : SiblingPath :=
  siblingPathOfList
    (tree.openingAt truncateSha256 leafDigest position.val).2
    (tree.openingAt_siblings_length truncateSha256 leafDigest position.val)

theorem PerfectTree.canonicalSiblingPath_as_list {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafDigest : Leaf → Digest208)
    (tree : PerfectTree Leaf treeDepth) (position : Position) :
    List.ofFn (tree.canonicalSiblingPath truncateSha256 leafDigest position) =
      (tree.openingAt truncateSha256 leafDigest position.val).2 := by
  exact ofFn_siblingPathOfList _ _

theorem PerfectTree.canonical_opening_authenticates {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafDigest : Leaf → Digest208)
    (tree : PerfectTree Leaf treeDepth) (position : Position) :
    foldPath truncateSha256 position
        (leafDigest
          (tree.openingAt truncateSha256 leafDigest position.val).1)
        (tree.canonicalSiblingPath truncateSha256 leafDigest position) =
      tree.root truncateSha256 leafDigest := by
  rw [foldPath, tree.canonicalSiblingPath_as_list]
  exact tree.openingAt_authenticates truncateSha256 leafDigest position.val

/-- Every independently committed complete word has a canonical opening at
each deployed query position.  Neither the leaf nor its siblings are supplied
by the verifier proof. -/
theorem commitTree_success_yields_canonical_opening {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafDigest : Leaf → Digest208)
    (leaves : List Leaf) (root : Digest208) (position : Position)
    (success : commitTree truncateSha256 leafDigest treeDepth leaves =
      some root) :
    ∃ leaf : Leaf, ∃ siblings : SiblingPath,
      leaves[position.val]? = some leaf ∧
        foldPath truncateSha256 position (leafDigest leaf) siblings = root := by
  obtain ⟨tree, treeLeaves, treeRoot⟩ :=
    commitTree_success_yields_perfect_tree truncateSha256 leafDigest treeDepth
      leaves root success
  subst leaves
  subst root
  let leaf :=
    (tree.openingAt truncateSha256 leafDigest position.val).1
  let siblings :=
    tree.canonicalSiblingPath truncateSha256 leafDigest position
  refine ⟨leaf, siblings, ?_, ?_⟩
  · exact tree.openingAt_leaf_is_getElem truncateSha256 leafDigest position.val
      position.isLt
  · exact tree.canonical_opening_authenticates truncateSha256 leafDigest
      position

#print axioms PerfectTree.leaves_length
#print axioms PerfectTree.commit_leaves
#print axioms commitTree_success_yields_perfect_tree
#print axioms PerfectTree.openingAt_siblings_length
#print axioms foldPathAux_append
#print axioms PerfectTree.openingAt_authenticates
#print axioms PerfectTree.openingAt_eq_of_low_bits_eq
#print axioms PerfectTree.openingAt_leaf_is_getElem
#print axioms ofFn_siblingPathOfList
#print axioms PerfectTree.canonical_opening_authenticates
#print axioms commitTree_success_yields_canonical_opening

end AspisPool.V7MerkleCanonicalOpening
