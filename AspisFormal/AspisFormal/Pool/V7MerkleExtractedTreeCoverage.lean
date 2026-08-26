import AspisFormal.Pool.V7MerklePerfectTreeTraceCoverage
import AspisFormal.Pool.V7MerkleParserRoundtrip
import AspisFormal.Pool.V7MerkleAcceptedOpeningProjection

/-!
# Source-covered perfect trees from the Tag-73 K1.2 query graph

Successful causal extraction reconstructs not only a complete word and root,
but a perfect tree whose every typed leaf/node preimage belongs to the shared
collision universe.  Canonical path coverage then follows without treating a
supplied authentication path as the committed word.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisPool.V7MerkleExtractedTreeCoverage

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleParserRoundtrip
open AspisPool.V7MerkleExtractedSubtreeCommitment
open AspisPool.V7MerkleOpeningBinding
open AspisPool.V7MerkleCanonicalOpening
open AspisPool.V7MerklePerfectTreeTraceCoverage
open AspisPool.V7MerkleAcceptedOpeningProjection

/-! ## Deduplication preserves the input set -/

theorem mem_deduplicateFirstAux_or_seen_iff
    (input : RawHashInput) : ∀
    (seen : List RawHashInput) (log : OrderedRawQueryLog),
    input ∈ seen ∨ input ∈ deduplicateFirstAux seen log ↔
      input ∈ seen ∨ input ∈ log := by
  intro seen log
  induction log generalizing seen with
  | nil => simp [deduplicateFirstAux]
  | cons head rest inductionHypothesis =>
      by_cases headSeen : head ∈ seen
      · simp only [deduplicateFirstAux, headSeen, ↓reduceIte,
          List.mem_cons]
        constructor
        · intro inputIn
          rcases (inductionHypothesis seen).mp inputIn with
            inputInSeen | inputInRest
          · exact Or.inl inputInSeen
          · exact Or.inr (Or.inr inputInRest)
        · intro inputIn
          apply (inductionHypothesis seen).mpr
          rcases inputIn with inputInSeen | inputIsHead | inputInRest
          · exact Or.inl inputInSeen
          · exact Or.inl (inputIsHead.symm ▸ headSeen)
          · exact Or.inr inputInRest
      · simp only [deduplicateFirstAux, headSeen, ↓reduceIte,
          List.mem_cons]
        have restExact := inductionHypothesis (head :: seen)
        simp only [List.mem_cons] at restExact
        aesop

theorem mem_deduplicateFirst_iff
    (input : RawHashInput) (log : OrderedRawQueryLog) :
    input ∈ deduplicateFirst log ↔ input ∈ log := by
  simpa [deduplicateFirst] using
    mem_deduplicateFirstAux_or_seen_iff input [] log

theorem shared_log_mem_collisionUniverse
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) {input : RawHashInput}
    (inputIn : input ∈ log) :
    input ∈ collisionUniverse truncateSha256 log := by
  unfold collisionUniverse
  rw [mem_deduplicateFirst_iff]
  simp [inputIn]

theorem c1_default_input_mem_collisionUniverse
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) {input : RawHashInput}
    (inputIn : input ∈ defaultC1SubtreeInputs truncateSha256 treeDepth) :
    input ∈ collisionUniverse truncateSha256 log := by
  unfold collisionUniverse
  rw [mem_deduplicateFirst_iff]
  simp [inputIn]

theorem c2_default_input_mem_collisionUniverse
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) {input : RawHashInput}
    (inputIn : input ∈ defaultC2SubtreeInputs truncateSha256 treeDepth) :
    input ∈ collisionUniverse truncateSha256 log := by
  unfold collisionUniverse
  rw [mem_deduplicateFirst_iff]
  simp [inputIn]

theorem defaultC1SubtreeInputs_mono
    (truncateSha256 : RawHashInput → Digest208) : ∀
    {smallHeight largeHeight : Nat}, smallHeight ≤ largeHeight →
      ∀ {input : RawHashInput},
        input ∈ defaultC1SubtreeInputs truncateSha256 smallHeight →
          input ∈ defaultC1SubtreeInputs truncateSha256 largeHeight := by
  intro smallHeight largeHeight heightLe input inputIn
  induction largeHeight with
  | zero =>
      have smallZero : smallHeight = 0 := by omega
      simpa [smallZero] using inputIn
  | succ largeHeight inductionHypothesis =>
      by_cases heightExact : smallHeight = largeHeight + 1
      · simpa [heightExact] using inputIn
      · have smaller : smallHeight ≤ largeHeight := by omega
        simp only [defaultC1SubtreeInputs, List.mem_append,
          List.mem_singleton]
        exact Or.inl (inductionHypothesis smaller)

theorem defaultC2SubtreeInputs_mono
    (truncateSha256 : RawHashInput → Digest208) : ∀
    {smallHeight largeHeight : Nat}, smallHeight ≤ largeHeight →
      ∀ {input : RawHashInput},
        input ∈ defaultC2SubtreeInputs truncateSha256 smallHeight →
          input ∈ defaultC2SubtreeInputs truncateSha256 largeHeight := by
  intro smallHeight largeHeight heightLe input inputIn
  induction largeHeight with
  | zero =>
      have smallZero : smallHeight = 0 := by omega
      simpa [smallZero] using inputIn
  | succ largeHeight inductionHypothesis =>
      by_cases heightExact : smallHeight = largeHeight + 1
      · simpa [heightExact] using inputIn
      · have smaller : smallHeight ≤ largeHeight := by omega
        simp only [defaultC2SubtreeInputs, List.mem_append,
          List.mem_singleton]
        exact Or.inl (inductionHypothesis smaller)

theorem getElem?_some_mem {α : Type*} (values : List α)
    (index : Nat) (value : α) (found : values[index]? = some value) :
    value ∈ values := by
  rw [List.getElem?_eq_some_iff] at found
  rcases found with ⟨within, valueExact⟩
  have member := List.getElem_mem within
  simpa [valueExact] using member

/-! ## Canonical-default perfect trees -/

def defaultC1PerfectTree : ∀ height : Nat, PerfectTree C1Leaf height
  | 0 => .leaf defaultC1Leaf
  | height + 1 =>
      .node (defaultC1PerfectTree height) (defaultC1PerfectTree height)

def defaultC2PerfectTree : ∀ height : Nat, PerfectTree C2Leaf height
  | 0 => .leaf defaultC2Leaf
  | height + 1 =>
      .node (defaultC2PerfectTree height) (defaultC2PerfectTree height)

theorem defaultC1PerfectTree_leaves : ∀ height : Nat,
    (defaultC1PerfectTree height).leaves =
      List.replicate (2 ^ height) defaultC1Leaf := by
  intro height
  induction height with
  | zero => simp [defaultC1PerfectTree, PerfectTree.leaves]
  | succ height inductionHypothesis =>
      simp only [defaultC1PerfectTree, PerfectTree.leaves,
        inductionHypothesis]
      rw [← List.replicate_add, pow_succ]
      congr 1
      omega

theorem defaultC2PerfectTree_leaves : ∀ height : Nat,
    (defaultC2PerfectTree height).leaves =
      List.replicate (2 ^ height) defaultC2Leaf := by
  intro height
  induction height with
  | zero => simp [defaultC2PerfectTree, PerfectTree.leaves]
  | succ height inductionHypothesis =>
      simp only [defaultC2PerfectTree, PerfectTree.leaves,
        inductionHypothesis]
      rw [← List.replicate_add, pow_succ]
      congr 1
      omega

theorem defaultC1PerfectTree_root
    (truncateSha256 : RawHashInput → Digest208) : ∀ height : Nat,
    (defaultC1PerfectTree height).root truncateSha256
        (c1LeafDigest truncateSha256) =
      defaultC1SubtreeDigest truncateSha256 height := by
  intro height
  induction height with
  | zero => rfl
  | succ height inductionHypothesis =>
      simp [defaultC1PerfectTree, PerfectTree.root,
        defaultC1SubtreeDigest, inductionHypothesis]

theorem defaultC2PerfectTree_root
    (truncateSha256 : RawHashInput → Digest208) : ∀ height : Nat,
    (defaultC2PerfectTree height).root truncateSha256
        (c2LeafDigest truncateSha256) =
      defaultC2SubtreeDigest truncateSha256 height := by
  intro height
  induction height with
  | zero => rfl
  | succ height inductionHypothesis =>
      simp [defaultC2PerfectTree, PerfectTree.root,
        defaultC2SubtreeDigest, inductionHypothesis]

def c1LeafInput (leaf : C1Leaf) : RawHashInput :=
  serialize (.c1Leaf leaf.value leaf.salt)

def c2LeafInput (leaf : C2Leaf) : RawHashInput :=
  serialize (.c2Leaf leaf.value leaf.salt)

theorem defaultC1PerfectTree_inputs_covered
    (truncateSha256 : RawHashInput → Digest208) : ∀ height : Nat,
    TraceIncludedInLog
      (perfectTreeRawInputs truncateSha256 c1LeafInput
        (defaultC1PerfectTree height))
      (defaultC1SubtreeInputs truncateSha256 height) := by
  intro height
  induction height with
  | zero =>
      intro input inputIn
      simpa [perfectTreeRawInputs, defaultC1PerfectTree,
        defaultC1SubtreeInputs, c1LeafInput] using inputIn
  | succ height inductionHypothesis =>
      intro input inputIn
      simp only [perfectTreeRawInputs, defaultC1PerfectTree,
        List.mem_append, List.mem_singleton] at inputIn
      simp only [defaultC1SubtreeInputs, List.mem_append,
        List.mem_singleton]
      rcases inputIn with (inputInLeft | inputInRight) | inputIsNode
      · exact Or.inl (inductionHypothesis input inputInLeft)
      · exact Or.inl (inductionHypothesis input inputInRight)
      · right
        have rootExact :
            (defaultC1PerfectTree height).root truncateSha256
                (fun leaf => truncateSha256 (c1LeafInput leaf)) =
              defaultC1SubtreeDigest truncateSha256 height := by
          exact defaultC1PerfectTree_root truncateSha256 height
        simpa only [rootExact] using inputIsNode

theorem defaultC2PerfectTree_inputs_covered
    (truncateSha256 : RawHashInput → Digest208) : ∀ height : Nat,
    TraceIncludedInLog
      (perfectTreeRawInputs truncateSha256 c2LeafInput
        (defaultC2PerfectTree height))
      (defaultC2SubtreeInputs truncateSha256 height) := by
  intro height
  induction height with
  | zero =>
      intro input inputIn
      simpa [perfectTreeRawInputs, defaultC2PerfectTree,
        defaultC2SubtreeInputs, c2LeafInput] using inputIn
  | succ height inductionHypothesis =>
      intro input inputIn
      simp only [perfectTreeRawInputs, defaultC2PerfectTree,
        List.mem_append, List.mem_singleton] at inputIn
      simp only [defaultC2SubtreeInputs, List.mem_append,
        List.mem_singleton]
      rcases inputIn with (inputInLeft | inputInRight) | inputIsNode
      · exact Or.inl (inductionHypothesis input inputInLeft)
      · exact Or.inl (inductionHypothesis input inputInRight)
      · right
        have rootExact :
            (defaultC2PerfectTree height).root truncateSha256
                (fun leaf => truncateSha256 (c2LeafInput leaf)) =
              defaultC2SubtreeDigest truncateSha256 height := by
          exact defaultC2PerfectTree_root truncateSha256 height
        simpa only [rootExact] using inputIsNode

/-! ## Successful causal extraction builds source-covered perfect trees -/

theorem c1_child_result_yields_covered_tree
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (height : Nat)
    (heightBound : height ≤ treeDepth)
    (inductionHypothesis : ∀ (expectedDigest : Digest208)
      (queryIndex : Nat) (leaves : List C1Leaf),
      extractC1Subtree truncateSha256 log height expectedDigest queryIndex =
          .leaves leaves →
        ∃ tree : PerfectTree C1Leaf height,
          tree.leaves = leaves ∧
            tree.root truncateSha256 (c1LeafDigest truncateSha256) =
              expectedDigest ∧
            TraceIncludedInLog
              (perfectTreeRawInputs truncateSha256 c1LeafInput tree)
              (collisionUniverse truncateSha256 log))
    (parentQueryIndex : Nat) (child : Digest208) (leaves : List C1Leaf)
    (success : c1ChildResult truncateSha256 log height parentQueryIndex child =
      .leaves leaves) :
    ∃ tree : PerfectTree C1Leaf height,
      tree.leaves = leaves ∧
        tree.root truncateSha256 (c1LeafDigest truncateSha256) = child ∧
        TraceIncludedInLog
          (perfectTreeRawInputs truncateSha256 c1LeafInput tree)
          (collisionUniverse truncateSha256 log) := by
  unfold c1ChildResult at success
  split at success
  · rename_i childDefault
    simp only [SubtreeResult.leaves.injEq] at success
    subst leaves
    refine ⟨defaultC1PerfectTree height,
      defaultC1PerfectTree_leaves height, ?_, ?_⟩
    · simpa [childDefault] using
        defaultC1PerfectTree_root truncateSha256 height
    · intro input inputIn
      apply c1_default_input_mem_collisionUniverse truncateSha256 log
      apply defaultC1SubtreeInputs_mono truncateSha256 heightBound
      exact defaultC1PerfectTree_inputs_covered truncateSha256 height
        input inputIn
  · split at success
    · rename_i childIndex reference
      exact inductionHypothesis child childIndex leaves success
    · contradiction
    · contradiction

theorem extracted_c1_subtree_yields_covered_tree
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) : ∀
    (height : Nat), height ≤ treeDepth →
      ∀ (expectedDigest : Digest208) (queryIndex : Nat)
        (leaves : List C1Leaf),
      extractC1Subtree truncateSha256 log height expectedDigest queryIndex =
          .leaves leaves →
        ∃ tree : PerfectTree C1Leaf height,
          tree.leaves = leaves ∧
            tree.root truncateSha256 (c1LeafDigest truncateSha256) =
              expectedDigest ∧
            TraceIncludedInLog
              (perfectTreeRawInputs truncateSha256 c1LeafInput tree)
              (collisionUniverse truncateSha256 log) := by
  intro height
  induction height with
  | zero =>
      intro _heightBound expectedDigest queryIndex leaves success
      cases inputAt : log[queryIndex]? with
      | none => simp [extractC1Subtree, inputAt] at success
      | some input =>
          by_cases answerExact : truncateSha256 input = expectedDigest
          · cases parsed : parseTypedPreimage input with
            | none =>
                simp [extractC1Subtree, inputAt, answerExact, parsed] at success
            | some typed =>
                cases typed with
                | c1Leaf value salt =>
                    simp [extractC1Subtree, inputAt, answerExact, parsed]
                      at success
                    subst leaves
                    have serialized := serialize_parse_typed_preimage input
                      (.c1Leaf value salt) parsed
                    refine ⟨.leaf ⟨value, salt⟩, rfl, ?_, ?_⟩
                    · simpa [PerfectTree.root, c1LeafDigest, serialized] using
                        answerExact
                    · intro rawInput rawInputIn
                      have inputInLog := getElem?_some_mem log queryIndex input
                        inputAt
                      have inputCovered := shared_log_mem_collisionUniverse
                        truncateSha256 log inputInLog
                      simp only [perfectTreeRawInputs, List.mem_singleton]
                        at rawInputIn
                      rw [rawInputIn, c1LeafInput, serialized]
                      exact inputCovered
                | c2Leaf value salt =>
                    simp [extractC1Subtree, inputAt, answerExact, parsed]
                      at success
                | node left right =>
                    simp [extractC1Subtree, inputAt, answerExact, parsed]
                      at success
          · simp [extractC1Subtree, inputAt, answerExact] at success
  | succ height inductionHypothesis =>
      intro heightBound expectedDigest queryIndex leaves success
      have childHeightBound : height ≤ treeDepth := by omega
      cases inputAt : log[queryIndex]? with
      | none => simp [extractC1Subtree, inputAt] at success
      | some input =>
          by_cases answerExact : truncateSha256 input = expectedDigest
          · cases parsed : parseTypedPreimage input with
            | none =>
                simp [extractC1Subtree, inputAt, answerExact, parsed] at success
            | some typed =>
                cases typed with
                | c1Leaf value salt =>
                    simp [extractC1Subtree, inputAt, answerExact, parsed]
                      at success
                | c2Leaf value salt =>
                    simp [extractC1Subtree, inputAt, answerExact, parsed]
                      at success
                | node left right =>
                    simp only [extractC1Subtree, inputAt, answerExact, parsed,
                      ↓reduceIte] at success
                    change
                      (match c1ChildResult truncateSha256 log height queryIndex
                          left with
                      | SubtreeResult.failure reason =>
                          SubtreeResult.failure reason
                      | SubtreeResult.leaves leftLeaves =>
                          match c1ChildResult truncateSha256 log height
                              queryIndex right with
                          | SubtreeResult.failure reason =>
                              SubtreeResult.failure reason
                          | SubtreeResult.leaves rightLeaves =>
                              SubtreeResult.leaves
                                (leftLeaves ++ rightLeaves)) =
                        SubtreeResult.leaves leaves at success
                    cases leftResult : c1ChildResult truncateSha256 log height
                        queryIndex left with
                    | failure reason => simp [leftResult] at success
                    | leaves leftLeaves =>
                        cases rightResult : c1ChildResult truncateSha256 log
                            height queryIndex right with
                        | failure reason =>
                            simp [leftResult, rightResult] at success
                        | leaves rightLeaves =>
                            simp [leftResult, rightResult] at success
                            subst leaves
                            obtain ⟨leftTree, leftLeavesExact, leftRootExact,
                                leftCovered⟩ :=
                              c1_child_result_yields_covered_tree
                                truncateSha256 log height childHeightBound
                                (inductionHypothesis childHeightBound)
                                queryIndex left leftLeaves leftResult
                            obtain ⟨rightTree, rightLeavesExact, rightRootExact,
                                rightCovered⟩ :=
                              c1_child_result_yields_covered_tree
                                truncateSha256 log height childHeightBound
                                (inductionHypothesis childHeightBound)
                                queryIndex right rightLeaves rightResult
                            have serialized := serialize_parse_typed_preimage
                              input (.node left right) parsed
                            have inputInLog := getElem?_some_mem log queryIndex
                              input inputAt
                            have inputCovered :=
                              shared_log_mem_collisionUniverse truncateSha256
                                log inputInLog
                            have leftInputRootExact :
                                leftTree.root truncateSha256
                                    (fun leaf => truncateSha256
                                      (c1LeafInput leaf)) = left := by
                              exact leftRootExact
                            have rightInputRootExact :
                                rightTree.root truncateSha256
                                    (fun leaf => truncateSha256
                                      (c1LeafInput leaf)) = right := by
                              exact rightRootExact
                            refine ⟨.node leftTree rightTree, ?_, ?_, ?_⟩
                            · simp [PerfectTree.leaves, leftLeavesExact,
                                rightLeavesExact]
                            · simp [PerfectTree.root, leftRootExact,
                                rightRootExact, nodeDigest, serialized,
                                answerExact]
                            · intro rawInput rawInputIn
                              simp only [perfectTreeRawInputs,
                                List.mem_append, List.mem_singleton]
                                at rawInputIn
                              rcases rawInputIn with
                                (rawInputInLeft | rawInputInRight) |
                                  rawInputIsNode
                              · exact leftCovered rawInput rawInputInLeft
                              · exact rightCovered rawInput rawInputInRight
                              · rw [rawInputIsNode, leftInputRootExact,
                                  rightInputRootExact, serialized]
                                exact inputCovered
          · simp [extractC1Subtree, inputAt, answerExact] at success

theorem c2_child_result_yields_covered_tree
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (height : Nat)
    (heightBound : height ≤ treeDepth)
    (inductionHypothesis : ∀ (expectedDigest : Digest208)
      (queryIndex : Nat) (leaves : List C2Leaf),
      extractC2Subtree truncateSha256 log height expectedDigest queryIndex =
          .leaves leaves →
        ∃ tree : PerfectTree C2Leaf height,
          tree.leaves = leaves ∧
            tree.root truncateSha256 (c2LeafDigest truncateSha256) =
              expectedDigest ∧
            TraceIncludedInLog
              (perfectTreeRawInputs truncateSha256 c2LeafInput tree)
              (collisionUniverse truncateSha256 log))
    (parentQueryIndex : Nat) (child : Digest208) (leaves : List C2Leaf)
    (success : c2ChildResult truncateSha256 log height parentQueryIndex child =
      .leaves leaves) :
    ∃ tree : PerfectTree C2Leaf height,
      tree.leaves = leaves ∧
        tree.root truncateSha256 (c2LeafDigest truncateSha256) = child ∧
        TraceIncludedInLog
          (perfectTreeRawInputs truncateSha256 c2LeafInput tree)
          (collisionUniverse truncateSha256 log) := by
  unfold c2ChildResult at success
  split at success
  · rename_i childDefault
    simp only [SubtreeResult.leaves.injEq] at success
    subst leaves
    refine ⟨defaultC2PerfectTree height,
      defaultC2PerfectTree_leaves height, ?_, ?_⟩
    · simpa [childDefault] using
        defaultC2PerfectTree_root truncateSha256 height
    · intro input inputIn
      apply c2_default_input_mem_collisionUniverse truncateSha256 log
      apply defaultC2SubtreeInputs_mono truncateSha256 heightBound
      exact defaultC2PerfectTree_inputs_covered truncateSha256 height
        input inputIn
  · split at success
    · rename_i childIndex reference
      exact inductionHypothesis child childIndex leaves success
    · contradiction
    · contradiction

theorem extracted_c2_subtree_yields_covered_tree
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) : ∀
    (height : Nat), height ≤ treeDepth →
      ∀ (expectedDigest : Digest208) (queryIndex : Nat)
        (leaves : List C2Leaf),
      extractC2Subtree truncateSha256 log height expectedDigest queryIndex =
          .leaves leaves →
        ∃ tree : PerfectTree C2Leaf height,
          tree.leaves = leaves ∧
            tree.root truncateSha256 (c2LeafDigest truncateSha256) =
              expectedDigest ∧
            TraceIncludedInLog
              (perfectTreeRawInputs truncateSha256 c2LeafInput tree)
              (collisionUniverse truncateSha256 log) := by
  intro height
  induction height with
  | zero =>
      intro _heightBound expectedDigest queryIndex leaves success
      cases inputAt : log[queryIndex]? with
      | none => simp [extractC2Subtree, inputAt] at success
      | some input =>
          by_cases answerExact : truncateSha256 input = expectedDigest
          · cases parsed : parseTypedPreimage input with
            | none =>
                simp [extractC2Subtree, inputAt, answerExact, parsed] at success
            | some typed =>
                cases typed with
                | c1Leaf value salt =>
                    simp [extractC2Subtree, inputAt, answerExact, parsed]
                      at success
                | c2Leaf value salt =>
                    simp [extractC2Subtree, inputAt, answerExact, parsed]
                      at success
                    subst leaves
                    have serialized := serialize_parse_typed_preimage input
                      (.c2Leaf value salt) parsed
                    refine ⟨.leaf ⟨value, salt⟩, rfl, ?_, ?_⟩
                    · simpa [PerfectTree.root, c2LeafDigest, serialized] using
                        answerExact
                    · intro rawInput rawInputIn
                      have inputInLog := getElem?_some_mem log queryIndex input
                        inputAt
                      have inputCovered := shared_log_mem_collisionUniverse
                        truncateSha256 log inputInLog
                      simp only [perfectTreeRawInputs, List.mem_singleton]
                        at rawInputIn
                      rw [rawInputIn, c2LeafInput, serialized]
                      exact inputCovered
                | node left right =>
                    simp [extractC2Subtree, inputAt, answerExact, parsed]
                      at success
          · simp [extractC2Subtree, inputAt, answerExact] at success
  | succ height inductionHypothesis =>
      intro heightBound expectedDigest queryIndex leaves success
      have childHeightBound : height ≤ treeDepth := by omega
      cases inputAt : log[queryIndex]? with
      | none => simp [extractC2Subtree, inputAt] at success
      | some input =>
          by_cases answerExact : truncateSha256 input = expectedDigest
          · cases parsed : parseTypedPreimage input with
            | none =>
                simp [extractC2Subtree, inputAt, answerExact, parsed] at success
            | some typed =>
                cases typed with
                | c1Leaf value salt =>
                    simp [extractC2Subtree, inputAt, answerExact, parsed]
                      at success
                | c2Leaf value salt =>
                    simp [extractC2Subtree, inputAt, answerExact, parsed]
                      at success
                | node left right =>
                    simp only [extractC2Subtree, inputAt, answerExact, parsed,
                      ↓reduceIte] at success
                    change
                      (match c2ChildResult truncateSha256 log height queryIndex
                          left with
                      | SubtreeResult.failure reason =>
                          SubtreeResult.failure reason
                      | SubtreeResult.leaves leftLeaves =>
                          match c2ChildResult truncateSha256 log height
                              queryIndex right with
                          | SubtreeResult.failure reason =>
                              SubtreeResult.failure reason
                          | SubtreeResult.leaves rightLeaves =>
                              SubtreeResult.leaves
                                (leftLeaves ++ rightLeaves)) =
                        SubtreeResult.leaves leaves at success
                    cases leftResult : c2ChildResult truncateSha256 log height
                        queryIndex left with
                    | failure reason => simp [leftResult] at success
                    | leaves leftLeaves =>
                        cases rightResult : c2ChildResult truncateSha256 log
                            height queryIndex right with
                        | failure reason =>
                            simp [leftResult, rightResult] at success
                        | leaves rightLeaves =>
                            simp [leftResult, rightResult] at success
                            subst leaves
                            obtain ⟨leftTree, leftLeavesExact, leftRootExact,
                                leftCovered⟩ :=
                              c2_child_result_yields_covered_tree
                                truncateSha256 log height childHeightBound
                                (inductionHypothesis childHeightBound)
                                queryIndex left leftLeaves leftResult
                            obtain ⟨rightTree, rightLeavesExact, rightRootExact,
                                rightCovered⟩ :=
                              c2_child_result_yields_covered_tree
                                truncateSha256 log height childHeightBound
                                (inductionHypothesis childHeightBound)
                                queryIndex right rightLeaves rightResult
                            have serialized := serialize_parse_typed_preimage
                              input (.node left right) parsed
                            have inputInLog := getElem?_some_mem log queryIndex
                              input inputAt
                            have inputCovered :=
                              shared_log_mem_collisionUniverse truncateSha256
                                log inputInLog
                            have leftInputRootExact :
                                leftTree.root truncateSha256
                                    (fun leaf => truncateSha256
                                      (c2LeafInput leaf)) = left := by
                              exact leftRootExact
                            have rightInputRootExact :
                                rightTree.root truncateSha256
                                    (fun leaf => truncateSha256
                                      (c2LeafInput leaf)) = right := by
                              exact rightRootExact
                            refine ⟨.node leftTree rightTree, ?_, ?_, ?_⟩
                            · simp [PerfectTree.leaves, leftLeavesExact,
                                rightLeavesExact]
                            · simp [PerfectTree.root, leftRootExact,
                                rightRootExact, nodeDigest, serialized,
                                answerExact]
                            · intro rawInput rawInputIn
                              simp only [perfectTreeRawInputs,
                                List.mem_append, List.mem_singleton]
                                at rawInputIn
                              rcases rawInputIn with
                                (rawInputInLeft | rawInputInRight) |
                                  rawInputIsNode
                              · exact leftCovered rawInput rawInputInLeft
                              · exact rightCovered rawInput rawInputInRight
                              · rw [rawInputIsNode, leftInputRootExact,
                                  rightInputRootExact, serialized]
                                exact inputCovered
          · simp [extractC2Subtree, inputAt, answerExact] at success

/-! ## Complete extracted words and their sixteen canonical openings -/

def CoveredCompleteTrees
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (words : ExtractedWords)
    (log : OrderedRawQueryLog) : Prop :=
  (∃ c1Tree : PerfectTree C1Leaf treeDepth,
      c1Tree.leaves = words.c1 ∧
        c1Tree.root truncateSha256 (c1LeafDigest truncateSha256) = roots.c1 ∧
        TraceIncludedInLog
          (perfectTreeRawInputs truncateSha256 c1LeafInput c1Tree) log) ∧
    ∃ c2Tree : PerfectTree C2Leaf treeDepth,
      c2Tree.leaves = words.c2 ∧
        c2Tree.root truncateSha256 (c2LeafDigest truncateSha256) = roots.c2 ∧
        TraceIncludedInLog
          (perfectTreeRawInputs truncateSha256 c2LeafInput c2Tree) log

theorem extractCompleteWords_success_yields_covered_trees
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (log : OrderedRawQueryLog) (words : ExtractedWords)
    (success : extractCompleteWords truncateSha256 roots log = .words words) :
    CoveredCompleteTrees truncateSha256 roots words
      (collisionUniverse truncateSha256 log) := by
  obtain ⟨c1RootIndex, c2RootIndex, _c1RootQuery, _c2RootQuery,
      c1Extraction, c2Extraction⟩ :=
    extractCompleteWords_success_yields_root_queries
      truncateSha256 roots log words success
  obtain ⟨c1Tree, c1Leaves, c1Root, c1Covered⟩ :=
    extracted_c1_subtree_yields_covered_tree truncateSha256 log treeDepth
      (by rfl) roots.c1 c1RootIndex words.c1 c1Extraction
  obtain ⟨c2Tree, c2Leaves, c2Root, c2Covered⟩ :=
    extracted_c2_subtree_yields_covered_tree truncateSha256 log treeDepth
      (by rfl) roots.c2 c2RootIndex words.c2 c2Extraction
  exact ⟨⟨c1Tree, c1Leaves, c1Root, c1Covered⟩,
    ⟨c2Tree, c2Leaves, c2Root, c2Covered⟩⟩

theorem c1_covered_tree_yields_canonical_opening
    (truncateSha256 : RawHashInput → Digest208)
    (words : List C1Leaf) (root : Digest208)
    (position : Position) (log : OrderedRawQueryLog)
    (tree : PerfectTree C1Leaf treeDepth)
    (leavesExact : tree.leaves = words)
    (rootExact :
      tree.root truncateSha256 (c1LeafDigest truncateSha256) = root)
    (covered : TraceIncludedInLog
      (perfectTreeRawInputs truncateSha256 c1LeafInput tree) log) :
    C1CoveredCanonicalOpening truncateSha256 words root position log := by
  let leaf :=
    (tree.openingAt truncateSha256 (c1LeafDigest truncateSha256)
      position.val).1
  let siblings :=
    tree.canonicalSiblingPath truncateSha256
      (c1LeafDigest truncateSha256) position
  have leafDigestExact :
      c1LeafDigest truncateSha256 =
        fun value => truncateSha256 (c1LeafInput value) := by
    rfl
  have leafExact : leaf =
      (tree.openingAt truncateSha256
        (fun value => truncateSha256 (c1LeafInput value)) position.val).1 := by
    dsimp only [leaf]
    rw [leafDigestExact]
  have siblingsExact : siblings =
      tree.canonicalSiblingPath truncateSha256
        (fun value => truncateSha256 (c1LeafInput value)) position := by
    dsimp only [siblings]
    rw [leafDigestExact]
  refine ⟨leaf, siblings, ?_, ?_, ?_⟩
  · rw [← leavesExact]
    exact tree.openingAt_leaf_is_getElem truncateSha256
      (c1LeafDigest truncateSha256) position.val position.isLt
  · exact (tree.canonical_opening_authenticates truncateSha256
      (c1LeafDigest truncateSha256) position).trans rootExact
  · intro input inputIn
    rw [leafExact, siblingsExact] at inputIn
    apply covered input
    apply perfectTreeCanonicalRawTrace_in_rawInputs truncateSha256
      c1LeafInput tree position.val input
    simpa [openingInputTrace, openingRawInputTrace,
      perfectTreeCanonicalRawTrace, leaf, siblings, c1LeafInput,
      leafDigestExact, PerfectTree.canonicalSiblingPath_as_list] using inputIn

theorem c2_covered_tree_yields_canonical_opening
    (truncateSha256 : RawHashInput → Digest208)
    (words : List C2Leaf) (root : Digest208)
    (position : Position) (log : OrderedRawQueryLog)
    (tree : PerfectTree C2Leaf treeDepth)
    (leavesExact : tree.leaves = words)
    (rootExact :
      tree.root truncateSha256 (c2LeafDigest truncateSha256) = root)
    (covered : TraceIncludedInLog
      (perfectTreeRawInputs truncateSha256 c2LeafInput tree) log) :
    C2CoveredCanonicalOpening truncateSha256 words root position log := by
  let leaf :=
    (tree.openingAt truncateSha256 (c2LeafDigest truncateSha256)
      position.val).1
  let siblings :=
    tree.canonicalSiblingPath truncateSha256
      (c2LeafDigest truncateSha256) position
  have leafDigestExact :
      c2LeafDigest truncateSha256 =
        fun value => truncateSha256 (c2LeafInput value) := by
    rfl
  have leafExact : leaf =
      (tree.openingAt truncateSha256
        (fun value => truncateSha256 (c2LeafInput value)) position.val).1 := by
    dsimp only [leaf]
    rw [leafDigestExact]
  have siblingsExact : siblings =
      tree.canonicalSiblingPath truncateSha256
        (fun value => truncateSha256 (c2LeafInput value)) position := by
    dsimp only [siblings]
    rw [leafDigestExact]
  refine ⟨leaf, siblings, ?_, ?_, ?_⟩
  · rw [← leavesExact]
    exact tree.openingAt_leaf_is_getElem truncateSha256
      (c2LeafDigest truncateSha256) position.val position.isLt
  · exact (tree.canonical_opening_authenticates truncateSha256
      (c2LeafDigest truncateSha256) position).trans rootExact
  · intro input inputIn
    rw [leafExact, siblingsExact] at inputIn
    apply covered input
    apply perfectTreeCanonicalRawTrace_in_rawInputs truncateSha256
      c2LeafInput tree position.val input
    simpa [openingInputTrace, openingRawInputTrace,
      perfectTreeCanonicalRawTrace, leaf, siblings, c2LeafInput,
      leafDigestExact, PerfectTree.canonicalSiblingPath_as_list] using inputIn

theorem covered_complete_trees_yield_all_canonical_openings
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (words : ExtractedWords)
    (log : OrderedRawQueryLog)
    (covered : CoveredCompleteTrees truncateSha256 roots words log) :
    (∀ position : Position,
      C1CoveredCanonicalOpening truncateSha256 words.c1 roots.c1
        position log) ∧
    (∀ position : Position,
      C2CoveredCanonicalOpening truncateSha256 words.c2 roots.c2
        position log) := by
  obtain ⟨⟨c1Tree, c1Leaves, c1Root, c1Covered⟩,
      ⟨c2Tree, c2Leaves, c2Root, c2Covered⟩⟩ := covered
  constructor
  · intro position
    exact c1_covered_tree_yields_canonical_opening truncateSha256 words.c1
      roots.c1 position log c1Tree c1Leaves c1Root c1Covered
  · intro position
    exact c2_covered_tree_yields_canonical_opening truncateSha256 words.c2
      roots.c2 position log c2Tree c2Leaves c2Root c2Covered

theorem extractV7Words_success_yields_collision_free_covered_trees
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (orderedQueries : OrderedRawQueryLog) (words : ExtractedWords)
    (success : extractV7Words truncateSha256 roots proof orderedQueries =
      .words words) :
    let log := deduplicateFirst orderedQueries
    hasRawTruncatedCollision truncateSha256
        (collisionUniverse truncateSha256 log) = false ∧
      CoveredCompleteTrees truncateSha256 roots words
        (collisionUniverse truncateSha256 log) := by
  have provenance := extractV7Words_success_yields_causal_provenance
    truncateSha256 roots proof orderedQueries words success
  unfold SuccessfulCausalProvenance at provenance
  dsimp only at provenance ⊢
  obtain ⟨noCollision, c1RootIndex, c2RootIndex, _c1RootQuery,
      _c2RootQuery, c1Extraction, c2Extraction, _projections⟩ := provenance
  obtain ⟨c1Tree, c1Leaves, c1Root, c1Covered⟩ :=
    extracted_c1_subtree_yields_covered_tree truncateSha256
      (deduplicateFirst orderedQueries) treeDepth (by rfl) roots.c1
      c1RootIndex words.c1 c1Extraction
  obtain ⟨c2Tree, c2Leaves, c2Root, c2Covered⟩ :=
    extracted_c2_subtree_yields_covered_tree truncateSha256
      (deduplicateFirst orderedQueries) treeDepth (by rfl) roots.c2
      c2RootIndex words.c2 c2Extraction
  exact ⟨noCollision,
    ⟨⟨c1Tree, c1Leaves, c1Root, c1Covered⟩,
      ⟨c2Tree, c2Leaves, c2Root, c2Covered⟩⟩⟩

theorem extractV7Words_success_yields_all_covered_canonical_openings
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (orderedQueries : OrderedRawQueryLog) (words : ExtractedWords)
    (success : extractV7Words truncateSha256 roots proof orderedQueries =
      .words words) :
    let log := deduplicateFirst orderedQueries
    hasRawTruncatedCollision truncateSha256
        (collisionUniverse truncateSha256 log) = false ∧
      (∀ position : Position,
        C1CoveredCanonicalOpening truncateSha256 words.c1 roots.c1 position
          (collisionUniverse truncateSha256 log)) ∧
      (∀ position : Position,
        C2CoveredCanonicalOpening truncateSha256 words.c2 roots.c2 position
          (collisionUniverse truncateSha256 log)) := by
  dsimp only
  obtain ⟨noCollision, coveredTrees⟩ :=
    extractV7Words_success_yields_collision_free_covered_trees
      truncateSha256 roots proof orderedQueries words success
  obtain ⟨c1Openings, c2Openings⟩ :=
    covered_complete_trees_yield_all_canonical_openings truncateSha256 roots
      words (collisionUniverse truncateSha256
        (deduplicateFirst orderedQueries)) coveredTrees
  exact ⟨noCollision, c1Openings, c2Openings⟩
#print axioms mem_deduplicateFirst_iff
#print axioms defaultC1PerfectTree_inputs_covered
#print axioms defaultC2PerfectTree_inputs_covered
#print axioms extracted_c1_subtree_yields_covered_tree
#print axioms extracted_c2_subtree_yields_covered_tree
#print axioms extractCompleteWords_success_yields_covered_trees
#print axioms c1_covered_tree_yields_canonical_opening
#print axioms c2_covered_tree_yields_canonical_opening
#print axioms extractV7Words_success_yields_collision_free_covered_trees
#print axioms extractV7Words_success_yields_all_covered_canonical_openings

end AspisPool.V7MerkleExtractedTreeCoverage
