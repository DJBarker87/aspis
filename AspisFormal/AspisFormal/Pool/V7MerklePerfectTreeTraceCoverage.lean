import AspisFormal.Pool.V7MerkleCanonicalOpening

/-!
# Canonical-path call coverage inside a perfect V7 Merkle tree

Every raw SHA input on the canonical authentication path of a committed word
is one of the leaf/node inputs used by that perfect tree.  This is the pure
tree half of the K1.2 causal-coverage proof.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisPool.V7MerklePerfectTreeTraceCoverage

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisPool.V7MerkleCanonicalOpening

universe u

def perfectTreeRawInputs {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafInput : Leaf → RawHashInput) :
    {height : Nat} → PerfectTree Leaf height → List RawHashInput
  | 0, .leaf value => [leafInput value]
  | _ + 1, .node left right =>
      perfectTreeRawInputs truncateSha256 leafInput left ++
        perfectTreeRawInputs truncateSha256 leafInput right ++
        [serialize (.node
          (left.root truncateSha256 (fun leaf => truncateSha256 (leafInput leaf)))
          (right.root truncateSha256
            (fun leaf => truncateSha256 (leafInput leaf))))]

def perfectTreeCanonicalRawTrace {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafInput : Leaf → RawHashInput)
    {height : Nat} (tree : PerfectTree Leaf height)
    (position : Nat) : List RawHashInput :=
  let opening := tree.openingAt truncateSha256
    (fun leaf => truncateSha256 (leafInput leaf)) position
  leafInput opening.1 ::
    foldPathInputTrace truncateSha256 position
      (truncateSha256 (leafInput opening.1)) opening.2

theorem perfectTreeCanonicalRawTrace_in_rawInputs {Leaf : Type u}
    (truncateSha256 : RawHashInput → Digest208)
    (leafInput : Leaf → RawHashInput) :
    ∀ {height : Nat} (tree : PerfectTree Leaf height) (position : Nat),
      TraceIncludedInLog
        (perfectTreeCanonicalRawTrace truncateSha256 leafInput tree position)
        (perfectTreeRawInputs truncateSha256 leafInput tree) := by
  intro height tree
  induction tree with
  | leaf value =>
      intro position input inputIn
      simpa [perfectTreeCanonicalRawTrace, perfectTreeRawInputs,
        PerfectTree.openingAt, foldPathInputTrace] using inputIn
  | @node height left right leftInduction rightInduction =>
      intro position
      let leafDigest : Leaf → Digest208 :=
        fun leaf => truncateSha256 (leafInput leaf)
      by_cases direction : position.testBit height
      · have topDirection :
            (position / 2 ^ height).testBit 0 = true := by
          rw [Nat.testBit_div_two_pow]
          simpa using direction
        have traceEquation :
            perfectTreeCanonicalRawTrace truncateSha256 leafInput
                (PerfectTree.node left right) position =
              perfectTreeCanonicalRawTrace truncateSha256 leafInput right
                  position ++
                [serialize (.node
                  (left.root truncateSha256 leafDigest)
                  (right.root truncateSha256 leafDigest))] := by
          simp only [perfectTreeCanonicalRawTrace, PerfectTree.openingAt,
            direction, ↓reduceIte]
          rw [foldPathInputTrace_append]
          have rightRootExact :=
            right.openingAt_authenticates truncateSha256 leafDigest position
          rw [show
            foldPathAux truncateSha256 position
                (truncateSha256
                  (leafInput
                    (right.openingAt truncateSha256 leafDigest position).1))
                (right.openingAt truncateSha256 leafDigest position).2 =
              right.root truncateSha256 leafDigest by
                simpa [leafDigest] using rightRootExact]
          rw [right.openingAt_siblings_length]
          simp [foldPathInputTrace, orderedNodeInput, topDirection,
            leafDigest]
        intro input inputIn
        rw [traceEquation] at inputIn
        simp only [perfectTreeRawInputs, List.mem_append, List.mem_singleton]
          at inputIn ⊢
        rcases inputIn with inputInRight | inputIsNode
        · exact Or.inl (Or.inr
            (rightInduction position input inputInRight))
        · exact Or.inr (by simpa [leafDigest] using inputIsNode)
      · have directionFalse : position.testBit height = false :=
          Bool.eq_false_iff.mpr direction
        have topDirection :
            (position / 2 ^ height).testBit 0 = false := by
          rw [Nat.testBit_div_two_pow]
          simpa using directionFalse
        have traceEquation :
            perfectTreeCanonicalRawTrace truncateSha256 leafInput
                (PerfectTree.node left right) position =
              perfectTreeCanonicalRawTrace truncateSha256 leafInput left
                  position ++
                [serialize (.node
                  (left.root truncateSha256 leafDigest)
                  (right.root truncateSha256 leafDigest))] := by
          simp [perfectTreeCanonicalRawTrace, PerfectTree.openingAt,
            directionFalse]
          rw [foldPathInputTrace_append]
          have leftRootExact :=
            left.openingAt_authenticates truncateSha256 leafDigest position
          rw [show
            foldPathAux truncateSha256 position
                (truncateSha256
                  (leafInput
                    (left.openingAt truncateSha256 leafDigest position).1))
                (left.openingAt truncateSha256 leafDigest position).2 =
              left.root truncateSha256 leafDigest by
                simpa [leafDigest] using leftRootExact]
          rw [left.openingAt_siblings_length]
          simp [foldPathInputTrace, orderedNodeInput, topDirection,
            leafDigest]
        intro input inputIn
        rw [traceEquation] at inputIn
        simp only [perfectTreeRawInputs, List.mem_append, List.mem_singleton]
          at inputIn ⊢
        rcases inputIn with inputInLeft | inputIsNode
        · exact Or.inl (Or.inl
            (leftInduction position input inputInLeft))
        · exact Or.inr (by simpa [leafDigest] using inputIsNode)

#print axioms perfectTreeCanonicalRawTrace_in_rawInputs

end AspisPool.V7MerklePerfectTreeTraceCoverage
