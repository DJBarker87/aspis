import AspisFormal.Pool.V7MerkleQueryExtractor

/-!
# Prefix locality of successful complete Merkle traversal

Once a root query lies in an earlier log prefix, every child used by a
successful deployed traversal lies at a strictly earlier index.  Appending
later SHA queries therefore cannot change the extracted subtree.  This is
the generic graph-locality half of the Tag-73 post-prover suffix argument.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisPool.V7MerkleCompletePrefixStability

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor

theorem resolveFirstAux_append_of_some
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208)
    (offset : Nat) (pre suffix : OrderedRawQueryLog) (index : Nat)
    (resolved : resolveFirstAux truncateSha256 target offset pre =
      some index) :
    resolveFirstAux truncateSha256 target offset (pre ++ suffix) =
      some index := by
  induction pre generalizing offset with
  | nil => simp [resolveFirstAux] at resolved
  | cons head tail ih =>
      by_cases hit : truncateSha256 head = target
      · simpa [resolveFirstAux, hit] using resolved
      · rw [resolveFirstAux_cons_miss truncateSha256 target offset head tail hit]
          at resolved
        change resolveFirstAux truncateSha256 target offset
          (head :: (tail ++ suffix)) = some index
        rw [resolveFirstAux_cons_miss truncateSha256 target offset head
          (tail ++ suffix) hit]
        exact ih (offset := offset + 1) resolved

theorem resolveFirst_append_of_some
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208)
    (pre suffix : OrderedRawQueryLog) (index : Nat)
    (resolved : resolveFirst truncateSha256 target pre = some index) :
    resolveFirst truncateSha256 target (pre ++ suffix) = some index := by
  exact resolveFirstAux_append_of_some truncateSha256 target 0 pre suffix
    index resolved

theorem resolveFirstAux_some_bounds
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208) :
    ∀ (offset : Nat) (log : OrderedRawQueryLog) (index : Nat),
      resolveFirstAux truncateSha256 target offset log = some index →
        offset ≤ index ∧ index < offset + log.length := by
  intro offset log
  induction log generalizing offset with
  | nil => simp [resolveFirstAux]
  | cons head tail ih =>
      intro index resolved
      by_cases hit : truncateSha256 head = target
      · simp [resolveFirstAux, hit] at resolved
        subst index
        simp
      · rw [resolveFirstAux_cons_miss truncateSha256 target offset head tail hit]
          at resolved
        have bounds := ih (offset + 1) index resolved
        exact ⟨by omega, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bounds.2⟩

theorem resolveFirst_some_lt_length
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208)
    (log : OrderedRawQueryLog) (index : Nat)
    (resolved : resolveFirst truncateSha256 target log = some index) :
    index < log.length := by
  have bounds := resolveFirstAux_some_bounds truncateSha256 target 0 log index
    resolved
  omega

theorem resolveFirstAux_prefix_of_append_some
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208) :
    ∀ (offset : Nat) (pre suffix : OrderedRawQueryLog) (index : Nat),
      resolveFirstAux truncateSha256 target offset (pre ++ suffix) =
          some index →
      index < offset + pre.length →
      resolveFirstAux truncateSha256 target offset pre = some index := by
  intro offset pre
  induction pre generalizing offset with
  | nil =>
      intro suffix index resolved inPrefix
      have bounds := resolveFirstAux_some_bounds truncateSha256 target offset
        suffix index resolved
      simp only [List.length_nil, Nat.add_zero] at inPrefix
      omega
  | cons head tail ih =>
      intro suffix index resolved inPrefix
      by_cases hit : truncateSha256 head = target
      · simp [resolveFirstAux, hit] at resolved ⊢
        exact resolved
      · change resolveFirstAux truncateSha256 target offset
          (head :: (tail ++ suffix)) = some index at resolved
        rw [resolveFirstAux_cons_miss truncateSha256 target offset head
          (tail ++ suffix) hit] at resolved
        rw [resolveFirstAux_cons_miss truncateSha256 target offset head tail hit]
        apply ih (offset := offset + 1) suffix index resolved
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using inPrefix

theorem resolveFirst_prefix_of_append_some
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208)
    (pre suffix : OrderedRawQueryLog) (index : Nat)
    (resolved : resolveFirst truncateSha256 target (pre ++ suffix) =
      some index)
    (inPrefix : index < pre.length) :
    resolveFirst truncateSha256 target pre = some index := by
  exact resolveFirstAux_prefix_of_append_some truncateSha256 target 0 pre
    suffix index resolved (by simpa using inPrefix)

theorem earlier_index_lt_parent
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208)
    (parentQueryIndex childIndex : Nat) (log : OrderedRawQueryLog)
    (earlier : classifyReference truncateSha256 target parentQueryIndex log =
      .earlier childIndex) :
    childIndex < parentQueryIndex := by
  unfold classifyReference at earlier
  generalize firstExact : resolveFirstAux truncateSha256 target 0
      (List.take parentQueryIndex log) = first at earlier
  cases first with
  | none =>
      cases suffixExact : resolveFirstAux truncateSha256 target
          parentQueryIndex (List.drop parentQueryIndex log) <;>
        simp [suffixExact] at earlier
  | some index =>
      simp only at earlier
      cases earlier
      have bounds := resolveFirstAux_some_bounds truncateSha256 target 0
        (List.take parentQueryIndex log) childIndex firstExact
      calc
        childIndex < (List.take parentQueryIndex log).length := by
          simpa using bounds.2
        _ ≤ parentQueryIndex := List.length_take_le _ _

/-- If the full traversal classifies a child as earlier than a parent which
already lies in the prefix, the prefix alone makes the identical
classification. -/
theorem classifyReference_prefix_of_append_earlier
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208)
    (parentQueryIndex childIndex : Nat)
    (pre suffix : OrderedRawQueryLog)
    (parentInPrefix : parentQueryIndex < pre.length)
    (earlier : classifyReference truncateSha256 target parentQueryIndex
      (pre ++ suffix) = .earlier childIndex) :
    classifyReference truncateSha256 target parentQueryIndex pre =
      .earlier childIndex := by
  unfold classifyReference at earlier ⊢
  rw [List.take_append_of_le_length (Nat.le_of_lt parentInPrefix)] at earlier
  generalize firstExact :
      resolveFirstAux truncateSha256 target 0
        (List.take parentQueryIndex pre) = first at earlier ⊢
  cases first with
  | none =>
      cases suffixExact : resolveFirstAux truncateSha256 target
          parentQueryIndex (List.drop parentQueryIndex (pre ++ suffix)) <;>
        simp [suffixExact] at earlier
  | some index => simpa using earlier

theorem extractC1Subtree_success_at_prefix_index
    (truncateSha256 : RawHashInput → Digest208)
    (pre suffix : OrderedRawQueryLog) :
    ∀ (height : Nat) (expectedDigest : Digest208) (queryIndex : Nat)
      (leaves : List C1Leaf),
      queryIndex < pre.length →
      extractC1Subtree truncateSha256 (pre ++ suffix) height expectedDigest
          queryIndex = .leaves leaves →
      extractC1Subtree truncateSha256 pre height expectedDigest queryIndex =
        .leaves leaves := by
  intro height
  induction height with
  | zero =>
      intro expectedDigest queryIndex leaves inPrefix success
      simpa [extractC1Subtree, List.getElem?_append_left inPrefix] using success
  | succ height ih =>
      intro expectedDigest queryIndex leaves inPrefix success
      simp only [extractC1Subtree] at success ⊢
      rw [List.getElem?_append_left inPrefix] at success
      generalize inputExact : pre[queryIndex]? = inputOption at success ⊢
      cases inputOption with
      | none => simp at success
      | some input =>
          simp only at success ⊢
          by_cases digestExact : truncateSha256 input = expectedDigest
          · simp only [digestExact, ↓reduceIte] at success ⊢
            generalize typedExact : parseTypedPreimage input = typedOption
              at success ⊢
            cases typedOption with
            | none =>
                simp at success
            | some typed =>
                cases typed with
                | c1Leaf value salt =>
                    simp at success
                | c2Leaf value salt =>
                    simp at success
                | node left right =>
                    simp only at success ⊢
                    let fullChild := fun child =>
                      if child = defaultC1SubtreeDigest truncateSha256 height then
                        SubtreeResult.leaves
                          (List.replicate (2 ^ height) defaultC1Leaf)
                      else
                        match classifyReference truncateSha256 child queryIndex
                            (pre ++ suffix) with
                        | .earlier childIndex =>
                            extractC1Subtree truncateSha256 (pre ++ suffix)
                              height child childIndex
                        | .forward _ => .failure .forwardReference
                        | .missing => .failure .missingPreimageQuery
                    let preChild := fun child =>
                      if child = defaultC1SubtreeDigest truncateSha256 height then
                        SubtreeResult.leaves
                          (List.replicate (2 ^ height) defaultC1Leaf)
                      else
                        match classifyReference truncateSha256 child queryIndex
                            pre with
                        | .earlier childIndex =>
                            extractC1Subtree truncateSha256 pre height child
                              childIndex
                        | .forward _ => .failure .forwardReference
                        | .missing => .failure .missingPreimageQuery
                    have childSuccess : ∀ child childLeaves,
                        fullChild child = .leaves childLeaves →
                          preChild child = .leaves childLeaves := by
                      intro child childLeaves childRun
                      by_cases isDefault : child =
                          defaultC1SubtreeDigest truncateSha256 height
                      · simpa [fullChild, preChild, isDefault] using childRun
                      · cases referenceExact : classifyReference truncateSha256
                            child queryIndex (pre ++ suffix) with
                        | earlier childIndex =>
                            have childEarlier : childIndex < queryIndex :=
                              earlier_index_lt_parent truncateSha256 child
                                queryIndex childIndex (pre ++ suffix)
                                referenceExact
                            have prefixReference :=
                              classifyReference_prefix_of_append_earlier
                                truncateSha256 child queryIndex childIndex pre
                                suffix inPrefix referenceExact
                            have childRun' : extractC1Subtree truncateSha256
                                (pre ++ suffix) height child childIndex =
                                  .leaves childLeaves := by
                              simpa [fullChild, isDefault, referenceExact] using
                                childRun
                            have prefixRun := ih child childIndex childLeaves
                              (lt_trans childEarlier inPrefix) childRun'
                            simpa [preChild, isDefault, prefixReference] using
                              prefixRun
                        | forward forwardIndex =>
                            simp [fullChild, isDefault, referenceExact] at childRun
                        | missing =>
                            simp [fullChild, isDefault, referenceExact] at childRun
                    change (match fullChild left with
                      | .failure reason => SubtreeResult.failure reason
                      | .leaves leftLeaves =>
                          match fullChild right with
                          | .failure reason => SubtreeResult.failure reason
                          | .leaves rightLeaves =>
                              SubtreeResult.leaves
                                (leftLeaves ++ rightLeaves)) =
                        SubtreeResult.leaves leaves at success
                    change (match preChild left with
                      | .failure reason => SubtreeResult.failure reason
                      | .leaves leftLeaves =>
                          match preChild right with
                          | .failure reason => SubtreeResult.failure reason
                          | .leaves rightLeaves =>
                              SubtreeResult.leaves
                                (leftLeaves ++ rightLeaves)) =
                        SubtreeResult.leaves leaves
                    cases leftRun : fullChild left with
                    | failure reason => simp [leftRun] at success
                    | leaves leftLeaves =>
                        have leftPrefix := childSuccess left leftLeaves leftRun
                        cases rightRun : fullChild right with
                        | failure reason => simp [leftRun, rightRun] at success
                        | leaves rightLeaves =>
                            have rightPrefix := childSuccess right rightLeaves
                              rightRun
                            have leavesExact : leftLeaves ++ rightLeaves =
                                leaves := by
                              simpa [leftRun, rightRun] using success
                            rw [leftPrefix, rightPrefix]
                            exact congrArg SubtreeResult.leaves leavesExact
          · simp only [digestExact, ↓reduceIte] at success ⊢
            simp at success

theorem extractC2Subtree_success_at_prefix_index
    (truncateSha256 : RawHashInput → Digest208)
    (pre suffix : OrderedRawQueryLog) :
    ∀ (height : Nat) (expectedDigest : Digest208) (queryIndex : Nat)
      (leaves : List C2Leaf),
      queryIndex < pre.length →
      extractC2Subtree truncateSha256 (pre ++ suffix) height expectedDigest
          queryIndex = .leaves leaves →
      extractC2Subtree truncateSha256 pre height expectedDigest queryIndex =
        .leaves leaves := by
  intro height
  induction height with
  | zero =>
      intro expectedDigest queryIndex leaves inPrefix success
      simpa [extractC2Subtree, List.getElem?_append_left inPrefix] using success
  | succ height ih =>
      intro expectedDigest queryIndex leaves inPrefix success
      simp only [extractC2Subtree] at success ⊢
      rw [List.getElem?_append_left inPrefix] at success
      generalize inputExact : pre[queryIndex]? = inputOption at success ⊢
      cases inputOption with
      | none => simp at success
      | some input =>
          simp only at success ⊢
          by_cases digestExact : truncateSha256 input = expectedDigest
          · simp only [digestExact, ↓reduceIte] at success ⊢
            generalize typedExact : parseTypedPreimage input = typedOption
              at success ⊢
            cases typedOption with
            | none => simp at success
            | some typed =>
                cases typed with
                | c1Leaf value salt => simp at success
                | c2Leaf value salt => simp at success
                | node left right =>
                    simp only at success ⊢
                    let fullChild := fun child =>
                      if child = defaultC2SubtreeDigest truncateSha256 height then
                        SubtreeResult.leaves
                          (List.replicate (2 ^ height) defaultC2Leaf)
                      else
                        match classifyReference truncateSha256 child queryIndex
                            (pre ++ suffix) with
                        | .earlier childIndex =>
                            extractC2Subtree truncateSha256 (pre ++ suffix)
                              height child childIndex
                        | .forward _ => .failure .forwardReference
                        | .missing => .failure .missingPreimageQuery
                    let preChild := fun child =>
                      if child = defaultC2SubtreeDigest truncateSha256 height then
                        SubtreeResult.leaves
                          (List.replicate (2 ^ height) defaultC2Leaf)
                      else
                        match classifyReference truncateSha256 child queryIndex
                            pre with
                        | .earlier childIndex =>
                            extractC2Subtree truncateSha256 pre height child
                              childIndex
                        | .forward _ => .failure .forwardReference
                        | .missing => .failure .missingPreimageQuery
                    have childSuccess : ∀ child childLeaves,
                        fullChild child = .leaves childLeaves →
                          preChild child = .leaves childLeaves := by
                      intro child childLeaves childRun
                      by_cases isDefault : child =
                          defaultC2SubtreeDigest truncateSha256 height
                      · simpa [fullChild, preChild, isDefault] using childRun
                      · cases referenceExact : classifyReference truncateSha256
                            child queryIndex (pre ++ suffix) with
                        | earlier childIndex =>
                            have childEarlier : childIndex < queryIndex :=
                              earlier_index_lt_parent truncateSha256 child
                                queryIndex childIndex (pre ++ suffix)
                                referenceExact
                            have prefixReference :=
                              classifyReference_prefix_of_append_earlier
                                truncateSha256 child queryIndex childIndex pre
                                suffix inPrefix referenceExact
                            have childRun' : extractC2Subtree truncateSha256
                                (pre ++ suffix) height child childIndex =
                                  .leaves childLeaves := by
                              simpa [fullChild, isDefault, referenceExact] using
                                childRun
                            have prefixRun := ih child childIndex childLeaves
                              (lt_trans childEarlier inPrefix) childRun'
                            simpa [preChild, isDefault, prefixReference] using
                              prefixRun
                        | forward forwardIndex =>
                            simp [fullChild, isDefault, referenceExact] at childRun
                        | missing =>
                            simp [fullChild, isDefault, referenceExact] at childRun
                    change (match fullChild left with
                      | .failure reason => SubtreeResult.failure reason
                      | .leaves leftLeaves =>
                          match fullChild right with
                          | .failure reason => SubtreeResult.failure reason
                          | .leaves rightLeaves =>
                              SubtreeResult.leaves
                                (leftLeaves ++ rightLeaves)) =
                        SubtreeResult.leaves leaves at success
                    change (match preChild left with
                      | .failure reason => SubtreeResult.failure reason
                      | .leaves leftLeaves =>
                          match preChild right with
                          | .failure reason => SubtreeResult.failure reason
                          | .leaves rightLeaves =>
                              SubtreeResult.leaves
                                (leftLeaves ++ rightLeaves)) =
                        SubtreeResult.leaves leaves
                    cases leftRun : fullChild left with
                    | failure reason => simp [leftRun] at success
                    | leaves leftLeaves =>
                        have leftPrefix := childSuccess left leftLeaves leftRun
                        cases rightRun : fullChild right with
                        | failure reason => simp [leftRun, rightRun] at success
                        | leaves rightLeaves =>
                            have rightPrefix := childSuccess right rightLeaves
                              rightRun
                            have leavesExact : leftLeaves ++ rightLeaves =
                                leaves := by
                              simpa [leftRun, rightRun] using success
                            rw [leftPrefix, rightPrefix]
                            exact congrArg SubtreeResult.leaves leavesExact
          · simp only [digestExact, ↓reduceIte] at success ⊢
            simp at success

theorem extractC1Subtree_success_outer_typed
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (height : Nat) (expectedDigest : Digest208)
    (queryIndex : Nat) (leaves : List C1Leaf)
    (success : extractC1Subtree truncateSha256 log height expectedDigest
      queryIndex = .leaves leaves) :
    ∃ input, log[queryIndex]? = some input ∧
      parseTypedPreimage input ≠ none := by
  cases height <;> simp only [extractC1Subtree] at success
  all_goals
    cases inputExact : log[queryIndex]? with
    | none => simp [inputExact] at success
    | some input =>
        by_cases digestExact : truncateSha256 input = expectedDigest
        · cases typedExact : parseTypedPreimage input with
          | none => simp [inputExact, digestExact, typedExact] at success
          | some typed => exact ⟨input, rfl, by simp [typedExact]⟩
        · simp [inputExact, digestExact] at success

theorem extractC2Subtree_success_outer_typed
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (height : Nat) (expectedDigest : Digest208)
    (queryIndex : Nat) (leaves : List C2Leaf)
    (success : extractC2Subtree truncateSha256 log height expectedDigest
      queryIndex = .leaves leaves) :
    ∃ input, log[queryIndex]? = some input ∧
      parseTypedPreimage input ≠ none := by
  cases height <;> simp only [extractC2Subtree] at success
  all_goals
    cases inputExact : log[queryIndex]? with
    | none => simp [inputExact] at success
    | some input =>
        by_cases digestExact : truncateSha256 input = expectedDigest
        · cases typedExact : parseTypedPreimage input with
          | none => simp [inputExact, digestExact, typedExact] at success
          | some typed => exact ⟨input, rfl, by simp [typedExact]⟩
        · simp [inputExact, digestExact] at success

theorem successful_c1_root_index_lt_prefix
    (truncateSha256 : RawHashInput → Digest208)
    (pre suffix : OrderedRawQueryLog) (height : Nat)
    (target : Digest208) (index : Nat) (leaves : List C1Leaf)
    (suffixUntyped : ∀ input ∈ suffix, parseTypedPreimage input = none)
    (run : extractC1Subtree truncateSha256 (pre ++ suffix) height target
      index = .leaves leaves) :
    index < pre.length := by
  obtain ⟨input, inputExact, typed⟩ :=
    extractC1Subtree_success_outer_typed truncateSha256 (pre ++ suffix)
      height target index leaves run
  by_contra outside
  have after : pre.length ≤ index := Nat.le_of_not_gt outside
  rw [List.getElem?_append_right after] at inputExact
  have member : input ∈ suffix := List.mem_of_getElem? inputExact
  exact typed (suffixUntyped input member)

theorem successful_c2_root_index_lt_prefix
    (truncateSha256 : RawHashInput → Digest208)
    (pre suffix : OrderedRawQueryLog) (height : Nat)
    (target : Digest208) (index : Nat) (leaves : List C2Leaf)
    (suffixUntyped : ∀ input ∈ suffix, parseTypedPreimage input = none)
    (run : extractC2Subtree truncateSha256 (pre ++ suffix) height target
      index = .leaves leaves) :
    index < pre.length := by
  obtain ⟨input, inputExact, typed⟩ :=
    extractC2Subtree_success_outer_typed truncateSha256 (pre ++ suffix)
      height target index leaves run
  by_contra outside
  have after : pre.length ≤ index := Nat.le_of_not_gt outside
  rw [List.getElem?_append_right after] at inputExact
  have member : input ∈ suffix := List.mem_of_getElem? inputExact
  exact typed (suffixUntyped input member)

/-- A successful complete two-tree extraction is insensitive to an appended
suffix containing no typed Merkle preimages.  No collision assumption is
needed: a suffix collision selected as a root would fail its outer parse. -/
theorem extractCompleteWords_success_of_append_untyped_raw
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (pre suffix : OrderedRawQueryLog)
    (words : ExtractedWords)
    (suffixUntyped : ∀ input ∈ suffix, parseTypedPreimage input = none)
    (success : extractCompleteWords truncateSha256 roots (pre ++ suffix) =
      .words words) :
    extractCompleteWords truncateSha256 roots pre = .words words := by
  obtain ⟨c1Index, c2Index, c1Resolved, c2Resolved, c1Run, c2Run⟩ :=
    extractCompleteWords_success_yields_root_queries truncateSha256 roots
      (pre ++ suffix) words success
  have c1InPrefix := successful_c1_root_index_lt_prefix truncateSha256 pre
    suffix treeDepth roots.c1 c1Index words.c1 suffixUntyped c1Run
  have c2InPrefix := successful_c2_root_index_lt_prefix truncateSha256 pre
    suffix treeDepth roots.c2 c2Index words.c2 suffixUntyped c2Run
  have c1ResolvedPrefix := resolveFirst_prefix_of_append_some truncateSha256
    roots.c1 pre suffix c1Index c1Resolved c1InPrefix
  have c2ResolvedPrefix := resolveFirst_prefix_of_append_some truncateSha256
    roots.c2 pre suffix c2Index c2Resolved c2InPrefix
  have c1RunPrefix := extractC1Subtree_success_at_prefix_index truncateSha256
    pre suffix treeDepth roots.c1 c1Index words.c1 c1InPrefix c1Run
  have c2RunPrefix := extractC2Subtree_success_at_prefix_index truncateSha256
    pre suffix treeDepth roots.c2 c2Index words.c2 c2InPrefix c2Run
  simp [extractCompleteWords, c1ResolvedPrefix, c2ResolvedPrefix,
    c1RunPrefix, c2RunPrefix]

theorem mem_deduplicateFirstAux_source
    (seen : List RawHashInput) : ∀ (log : OrderedRawQueryLog) input,
      input ∈ deduplicateFirstAux seen log → input ∈ log := by
  intro log
  induction log generalizing seen with
  | nil => simp [deduplicateFirstAux]
  | cons head tail ih =>
      intro input member
      by_cases duplicate : head ∈ seen
      · simp only [deduplicateFirstAux, duplicate, ↓reduceIte] at member
        exact List.mem_cons_of_mem head (ih (seen := seen) input member)
      · simp only [deduplicateFirstAux, duplicate, ↓reduceIte,
          List.mem_cons] at member
        rcases member with rfl | member
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem head
            (ih (seen := head :: seen) input member)

theorem deduplicateFirstAux_append_decompose
    (seen : List RawHashInput) : ∀ (pre suffix : OrderedRawQueryLog),
      ∃ tail,
        deduplicateFirstAux seen (pre ++ suffix) =
          deduplicateFirstAux seen pre ++ tail ∧
        ∀ input ∈ tail, input ∈ suffix := by
  intro pre
  induction pre generalizing seen with
  | nil =>
      intro suffix
      refine ⟨deduplicateFirstAux seen suffix, rfl, ?_⟩
      intro input member
      exact mem_deduplicateFirstAux_source seen suffix input member
  | cons head rest ih =>
      intro suffix
      by_cases duplicate : head ∈ seen
      · obtain ⟨tail, exactAppend, tailSource⟩ := ih (seen := seen) suffix
        refine ⟨tail, ?_, tailSource⟩
        simpa [deduplicateFirstAux, duplicate] using exactAppend
      · obtain ⟨tail, exactAppend, tailSource⟩ :=
          ih (seen := head :: seen) suffix
        refine ⟨tail, ?_, tailSource⟩
        simpa [deduplicateFirstAux, duplicate] using
          congrArg (List.cons head) exactAppend

theorem deduplicateFirst_append_decompose
    (pre suffix : OrderedRawQueryLog) :
    ∃ tail,
      deduplicateFirst (pre ++ suffix) = deduplicateFirst pre ++ tail ∧
      ∀ input ∈ tail, input ∈ suffix := by
  exact deduplicateFirstAux_append_decompose [] pre suffix

/-- Public form used by K1.2/K1.3: later non-Merkle transcript queries can
be stripped even though the production extractor first deduplicates the
entire shared SHA log. -/
theorem extractCompleteWords_success_of_append_untyped
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (pre suffix : OrderedRawQueryLog)
    (words : ExtractedWords)
    (suffixUntyped : ∀ input ∈ suffix, parseTypedPreimage input = none)
    (success : extractCompleteWords truncateSha256 roots
      (deduplicateFirst (pre ++ suffix)) = .words words) :
    extractCompleteWords truncateSha256 roots (deduplicateFirst pre) =
      .words words := by
  obtain ⟨tail, deduplicated, tailSource⟩ :=
    deduplicateFirst_append_decompose pre suffix
  have tailUntyped : ∀ input ∈ tail, parseTypedPreimage input = none := by
    intro input member
    exact suffixUntyped input (tailSource input member)
  rw [deduplicated] at success
  exact extractCompleteWords_success_of_append_untyped_raw truncateSha256
    roots (deduplicateFirst pre) tail words tailUntyped success

#print axioms resolveFirstAux_some_bounds
#print axioms classifyReference_prefix_of_append_earlier
#print axioms extractC1Subtree_success_at_prefix_index
#print axioms extractC2Subtree_success_at_prefix_index
#print axioms successful_c1_root_index_lt_prefix
#print axioms successful_c2_root_index_lt_prefix
#print axioms extractCompleteWords_success_of_append_untyped_raw
#print axioms deduplicateFirst_append_decompose
#print axioms extractCompleteWords_success_of_append_untyped

end AspisPool.V7MerkleCompletePrefixStability
