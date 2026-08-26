import AspisFormal.Pool.V7MerkleRawCollisionPredicate

/-!
# Same-position binding for Tag-73 binary Merkle openings

This is the deterministic collision reduction used by K1.2.  Two paths may
carry completely different siblings, but if they use the same public
position, start from different leaf digests, and finish at the same root,
then one exact `0x11 || left[26] || right[26]` compression input collided.

The collision witness remains explicit.  A later source/history theorem must
show that both witnessed raw inputs occur in the shared oracle log before the
finite-query random-oracle bound is applied.
-/

set_option autoImplicit false

namespace AspisPool.V7MerkleOpeningBinding

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor

/-- A collision between arbitrary raw inputs.  This is only the deterministic
witness shape; the bounded event additionally records membership of both
inputs in the shared query history. -/
def GlobalRawTruncatedDigestCollision
    (truncateSha256 : RawHashInput → Digest208) : Prop :=
  ∃ left right : RawHashInput,
    left ≠ right ∧ truncateSha256 left = truncateSha256 right

def orderedNodeInput (position : Nat)
    (current sibling : Digest208) : RawHashInput :=
  if position.testBit 0 then
    serialize (.node sibling current)
  else
    serialize (.node current sibling)

/-- Exact bottom-up raw node calls made by one authentication path. -/
def foldPathInputTrace (truncateSha256 : RawHashInput → Digest208) :
    Nat → Digest208 → List Digest208 → List RawHashInput
  | _, _, [] => []
  | position, current, sibling :: rest =>
      let input := orderedNodeInput position current sibling
      input :: foldPathInputTrace truncateSha256 (position / 2)
        (truncateSha256 input) rest

def openingInputTrace (truncateSha256 : RawHashInput → Digest208)
    (position : Position) (leaf : TypedPreimage)
    (siblings : SiblingPath) : List RawHashInput :=
  let leafInput := serialize leaf
  leafInput :: foldPathInputTrace truncateSha256 position.val
    (truncateSha256 leafInput) (List.ofFn siblings)

/-- A collision whose left and right preimages are explicitly located in two
concrete authentication-call traces. -/
def CrossTraceRawCollision
    (truncateSha256 : RawHashInput → Digest208)
    (leftTrace rightTrace : List RawHashInput) : Prop :=
  ∃ left ∈ leftTrace, ∃ right ∈ rightTrace,
    left ≠ right ∧ truncateSha256 left = truncateSha256 right

theorem foldPathAux_cons
    (truncateSha256 : RawHashInput → Digest208)
    (position : Nat) (current sibling : Digest208)
    (rest : List Digest208) :
    foldPathAux truncateSha256 position current (sibling :: rest) =
      foldPathAux truncateSha256 (position / 2)
        (truncateSha256 (orderedNodeInput position current sibling)) rest := by
  by_cases direction : position.testBit 0
  · simp [foldPathAux, orderedNodeInput, direction]
  · simp [foldPathAux, orderedNodeInput, direction]

theorem ordered_node_input_ne_of_current_ne
    (position : Nat) {leftCurrent rightCurrent : Digest208}
    (differentCurrent : leftCurrent ≠ rightCurrent)
    (leftSibling rightSibling : Digest208) :
    orderedNodeInput position leftCurrent leftSibling ≠
      orderedNodeInput position rightCurrent rightSibling := by
  unfold orderedNodeInput
  split
  · intro equalInputs
    have equalNodes := serialize_injective equalInputs
    injection equalNodes with _ equalCurrent
    exact differentCurrent equalCurrent
  · intro equalInputs
    have equalNodes := serialize_injective equalInputs
    injection equalNodes with equalCurrent _
    exact differentCurrent equalCurrent

/-- Different running digests that become equal after binary paths with the
same public position and depth expose a concrete raw SHA-prefix collision.
The two sibling lists need only have the same length. -/
theorem foldPathAux_collision_of_current_ne_of_eq
    (truncateSha256 : RawHashInput → Digest208) :
    ∀ (leftSiblings : List Digest208),
      ∀ (position : Nat) (leftCurrent rightCurrent : Digest208)
        (rightSiblings : List Digest208),
        leftSiblings.length = rightSiblings.length →
        leftCurrent ≠ rightCurrent →
        foldPathAux truncateSha256 position leftCurrent leftSiblings =
          foldPathAux truncateSha256 position rightCurrent rightSiblings →
        GlobalRawTruncatedDigestCollision truncateSha256 := by
  intro leftSiblings
  induction leftSiblings with
  | nil =>
      intro position leftCurrent rightCurrent rightSiblings sameLength
        differentCurrent sameRoot
      have rightEmpty : rightSiblings = [] := by
        simpa using sameLength.symm
      subst rightSiblings
      exact False.elim (differentCurrent sameRoot)
  | cons leftSibling leftRest inductionHypothesis =>
      intro position leftCurrent rightCurrent rightSiblings sameLength
        differentCurrent sameRoot
      cases rightSiblings with
      | nil => simp at sameLength
      | cons rightSibling rightRest =>
          have restLength : leftRest.length = rightRest.length := by
            simpa using sameLength
          let leftInput := orderedNodeInput position leftCurrent leftSibling
          let rightInput := orderedNodeInput position rightCurrent rightSibling
          have differentInput : leftInput ≠ rightInput := by
            exact ordered_node_input_ne_of_current_ne position differentCurrent
              leftSibling rightSibling
          by_cases equalParent :
              truncateSha256 leftInput = truncateSha256 rightInput
          · exact ⟨leftInput, rightInput, differentInput, equalParent⟩
          · apply inductionHypothesis (position / 2)
              (truncateSha256 leftInput) (truncateSha256 rightInput)
              rightRest restLength equalParent
            simpa [foldPathAux_cons, leftInput, rightInput] using sameRoot

/-- Trace-preserving form of the binary-path collision reduction. -/
theorem foldPathAux_cross_trace_collision_of_current_ne_of_eq
    (truncateSha256 : RawHashInput → Digest208) :
    ∀ (leftSiblings : List Digest208),
      ∀ (position : Nat) (leftCurrent rightCurrent : Digest208)
        (rightSiblings : List Digest208),
        leftSiblings.length = rightSiblings.length →
        leftCurrent ≠ rightCurrent →
        foldPathAux truncateSha256 position leftCurrent leftSiblings =
          foldPathAux truncateSha256 position rightCurrent rightSiblings →
        CrossTraceRawCollision truncateSha256
          (foldPathInputTrace truncateSha256 position leftCurrent leftSiblings)
          (foldPathInputTrace truncateSha256 position rightCurrent
            rightSiblings) := by
  intro leftSiblings
  induction leftSiblings with
  | nil =>
      intro position leftCurrent rightCurrent rightSiblings sameLength
        differentCurrent sameRoot
      have rightEmpty : rightSiblings = [] := by
        simpa using sameLength.symm
      subst rightSiblings
      exact False.elim (differentCurrent sameRoot)
  | cons leftSibling leftRest inductionHypothesis =>
      intro position leftCurrent rightCurrent rightSiblings sameLength
        differentCurrent sameRoot
      cases rightSiblings with
      | nil => simp at sameLength
      | cons rightSibling rightRest =>
          have restLength : leftRest.length = rightRest.length := by
            simpa using sameLength
          let leftInput := orderedNodeInput position leftCurrent leftSibling
          let rightInput := orderedNodeInput position rightCurrent rightSibling
          have differentInput : leftInput ≠ rightInput := by
            exact ordered_node_input_ne_of_current_ne position differentCurrent
              leftSibling rightSibling
          by_cases equalParent :
              truncateSha256 leftInput = truncateSha256 rightInput
          · exact ⟨leftInput, by simp [foldPathInputTrace, leftInput],
              rightInput, by simp [foldPathInputTrace, rightInput],
              differentInput, equalParent⟩
          · obtain ⟨collisionLeft, collisionLeftIn, collisionRight,
                collisionRightIn, collisionInputsDifferent,
                collisionAnswersEqual⟩ :=
              inductionHypothesis (position / 2)
                (truncateSha256 leftInput) (truncateSha256 rightInput)
                rightRest restLength equalParent (by
                  simpa [foldPathAux_cons, leftInput, rightInput]
                    using sameRoot)
            exact ⟨collisionLeft,
              by
                simp only [foldPathInputTrace, List.mem_cons]
                exact Or.inr (by simpa [leftInput] using collisionLeftIn),
              collisionRight,
              by
                simp only [foldPathInputTrace, List.mem_cons]
                exact Or.inr (by simpa [rightInput] using collisionRightIn),
              collisionInputsDifferent, collisionAnswersEqual⟩

/-- If two distinct typed leaves at one public position authenticate to the
same root, either their leaf calls collide directly or a node call on the two
paths collides. -/
theorem same_position_distinct_typed_leaves_expose_raw_collision
    (truncateSha256 : RawHashInput → Digest208)
    (position : Position)
    (leftLeaf rightLeaf : TypedPreimage)
    (leftSiblings rightSiblings : SiblingPath)
    (differentLeaf : leftLeaf ≠ rightLeaf)
    (sameRoot :
      foldPath truncateSha256 position
          (truncateSha256 (serialize leftLeaf)) leftSiblings =
        foldPath truncateSha256 position
          (truncateSha256 (serialize rightLeaf)) rightSiblings) :
    GlobalRawTruncatedDigestCollision truncateSha256 := by
  have differentInput : serialize leftLeaf ≠ serialize rightLeaf := by
    exact fun equalInputs => differentLeaf (serialize_injective equalInputs)
  by_cases equalLeafDigest :
      truncateSha256 (serialize leftLeaf) =
        truncateSha256 (serialize rightLeaf)
  · exact ⟨serialize leftLeaf, serialize rightLeaf, differentInput,
      equalLeafDigest⟩
  · apply foldPathAux_collision_of_current_ne_of_eq truncateSha256
      (List.ofFn leftSiblings) position.val
      (truncateSha256 (serialize leftLeaf))
      (truncateSha256 (serialize rightLeaf))
      (List.ofFn rightSiblings)
    · simp
    · exact equalLeafDigest
    · exact sameRoot

/-- Strong source-facing result: both collision preimages are members of the
two exact typed-leaf-plus-node call traces. -/
theorem same_position_distinct_typed_leaves_expose_cross_trace_collision
    (truncateSha256 : RawHashInput → Digest208)
    (position : Position)
    (leftLeaf rightLeaf : TypedPreimage)
    (leftSiblings rightSiblings : SiblingPath)
    (differentLeaf : leftLeaf ≠ rightLeaf)
    (sameRoot :
      foldPath truncateSha256 position
          (truncateSha256 (serialize leftLeaf)) leftSiblings =
        foldPath truncateSha256 position
          (truncateSha256 (serialize rightLeaf)) rightSiblings) :
    CrossTraceRawCollision truncateSha256
      (openingInputTrace truncateSha256 position leftLeaf leftSiblings)
      (openingInputTrace truncateSha256 position rightLeaf rightSiblings) := by
  have differentInput : serialize leftLeaf ≠ serialize rightLeaf := by
    exact fun equalInputs => differentLeaf (serialize_injective equalInputs)
  by_cases equalLeafDigest :
      truncateSha256 (serialize leftLeaf) =
        truncateSha256 (serialize rightLeaf)
  · exact ⟨serialize leftLeaf, by simp [openingInputTrace],
      serialize rightLeaf, by simp [openingInputTrace], differentInput,
      equalLeafDigest⟩
  · obtain ⟨collisionLeft, collisionLeftIn, collisionRight,
        collisionRightIn, collisionInputsDifferent, collisionAnswersEqual⟩ :=
      foldPathAux_cross_trace_collision_of_current_ne_of_eq truncateSha256
        (List.ofFn leftSiblings) position.val
        (truncateSha256 (serialize leftLeaf))
        (truncateSha256 (serialize rightLeaf))
        (List.ofFn rightSiblings) (by simp) equalLeafDigest sameRoot
    exact ⟨collisionLeft,
      by
        simp only [openingInputTrace, List.mem_cons]
        exact Or.inr collisionLeftIn,
      collisionRight,
      by
        simp only [openingInputTrace, List.mem_cons]
        exact Or.inr collisionRightIn,
      collisionInputsDifferent, collisionAnswersEqual⟩

#print axioms ordered_node_input_ne_of_current_ne
#print axioms foldPathAux_collision_of_current_ne_of_eq
#print axioms foldPathAux_cross_trace_collision_of_current_ne_of_eq
#print axioms same_position_distinct_typed_leaves_expose_raw_collision
#print axioms same_position_distinct_typed_leaves_expose_cross_trace_collision

end AspisPool.V7MerkleOpeningBinding
