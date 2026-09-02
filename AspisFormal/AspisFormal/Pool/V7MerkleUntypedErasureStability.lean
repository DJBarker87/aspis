import AspisFormal.Pool.V7MerkleCompletePrefixStability
import AspisFormal.Pool.V7MerkleExtractedTreeCoverage
import AspisFormal.Pool.V7MerkleRawCollisionPredicate

/-!
# Order-preserving erasure of non-Merkle SHA queries

The restored Tag-73 fibre changes a small set of routed transcript queries,
but an adversary may place those queries anywhere in its chronological SHA
log.  Prefix locality is therefore insufficient: we need to erase the routed
queries in place while retaining every intervening Merkle query.

This module starts that stronger proof with the two facts used at every
recursive traversal node:

* deleting the pivot in `pre ++ pivot :: suffix` is exactly `pre ++ suffix`;
* in a collision-free log, an untyped pivot cannot have the digest of a typed
  Merkle preimage in the same log.

The later traversal theorem can consequently shift indices across the erased
pivot without assuming that the pivot occurred after the prover's Merkle
queries or that the verifier exposed it first.
-/

set_option autoImplicit false

namespace AspisPool.V7MerkleUntypedErasureStability

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleCompletePrefixStability
open AspisPool.V7MerkleExtractedTreeCoverage
open AspisPool.V7MerkleRawCollisionPredicate

/-- Erasing the distinguished pivot preserves the exact order of all other
queries. -/
theorem eraseIdx_pivot_append
    (pre suffix : OrderedRawQueryLog) (pivot : RawHashInput) :
    (pre ++ pivot :: suffix).eraseIdx pre.length = pre ++ suffix := by
  rw [List.eraseIdx_eq_take_drop_succ]
  simp

/-- Absence of the executable collision event makes the truncated digest
function injective on members of the audited log. -/
theorem truncate_injective_on_log_of_no_collision
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog)
    (noCollision : hasRawTruncatedCollision truncateSha256 log = false)
    {left right : RawHashInput}
    (leftMem : left ∈ log) (rightMem : right ∈ log)
    (digestExact : truncateSha256 left = truncateSha256 right) :
    left = right := by
  by_contra distinct
  have collision : RawLogTruncatedDigestCollision truncateSha256 log :=
    ⟨left, leftMem, right, rightMem, distinct, digestExact⟩
  exact ((no_raw_truncated_collision_iff truncateSha256 log).mp noCollision)
    collision

/-- A routed non-Merkle query cannot shadow any typed Merkle query under a
collision-free 208-bit view.  This is the precise replacement for the false
assumption that all routed queries form a suffix. -/
theorem untyped_pivot_digest_ne_typed_member
    (truncateSha256 : RawHashInput → Digest208)
    (pre suffix : OrderedRawQueryLog) (pivot typed : RawHashInput)
    (noCollision : hasRawTruncatedCollision truncateSha256
      (pre ++ pivot :: suffix) = false)
    (pivotUntyped : parseTypedPreimage pivot = none)
    (typedMem : typed ∈ pre ++ pivot :: suffix)
    (typedExact : parseTypedPreimage typed ≠ none) :
    truncateSha256 pivot ≠ truncateSha256 typed := by
  intro digestExact
  have pivotMem : pivot ∈ pre ++ pivot :: suffix := by simp
  have inputExact := truncate_injective_on_log_of_no_collision truncateSha256
    (pre ++ pivot :: suffix) noCollision pivotMem typedMem digestExact
  subst typed
  exact typedExact pivotUntyped

/-- The previous result in the orientation used by `resolveFirst`: a target
digest known to come from a typed log member cannot match the erased pivot. -/
theorem untyped_pivot_ne_typed_target
    (truncateSha256 : RawHashInput → Digest208)
    (pre suffix : OrderedRawQueryLog) (pivot typed : RawHashInput)
    (target : Digest208)
    (noCollision : hasRawTruncatedCollision truncateSha256
      (pre ++ pivot :: suffix) = false)
    (pivotUntyped : parseTypedPreimage pivot = none)
    (typedMem : typed ∈ pre ++ pivot :: suffix)
    (typedExact : parseTypedPreimage typed ≠ none)
    (targetExact : truncateSha256 typed = target) :
    truncateSha256 pivot ≠ target := by
  rw [← targetExact]
  exact untyped_pivot_digest_ne_typed_member truncateSha256 pre suffix pivot
    typed noCollision pivotUntyped typedMem typedExact

/-! ## Exact index transport across one erased query -/

/-- Embed an index of the shortened log back into the original log. -/
def liftErasedIndex (pivot index : Nat) : Nat :=
  if index < pivot then index else index + 1

/-- Project a non-pivot index of the original log into the shortened log. -/
def lowerErasedIndex (pivot index : Nat) : Nat :=
  if index < pivot then index else index - 1

@[simp] theorem lowerErasedIndex_liftErasedIndex (pivot index : Nat) :
    lowerErasedIndex pivot (liftErasedIndex pivot index) = index := by
  by_cases before : index < pivot
  · simp [lowerErasedIndex, liftErasedIndex, before]
  · have after : pivot ≤ index := Nat.le_of_not_gt before
    simp [lowerErasedIndex, liftErasedIndex, before]
    omega

theorem liftErasedIndex_lowerErasedIndex_of_ne
    (pivot index : Nat) (notPivot : index ≠ pivot) :
    liftErasedIndex pivot (lowerErasedIndex pivot index) = index := by
  by_cases before : index < pivot
  · simp [lowerErasedIndex, liftErasedIndex, before]
  · have after : pivot < index := Nat.lt_of_le_of_ne
      (Nat.le_of_not_gt before) (Ne.symm notPivot)
    have loweredAfter : ¬ index - 1 < pivot := by omega
    simp [lowerErasedIndex, liftErasedIndex, before, loweredAfter]
    omega

/-- `getElem?` at a shortened-log index is exactly `getElem?` at its embedded
original-log index. -/
theorem getElem?_erase_pivot_lift
    (pre suffix : OrderedRawQueryLog) (pivot : RawHashInput) (index : Nat) :
    (pre ++ pivot :: suffix)[liftErasedIndex pre.length index]? =
      (pre ++ suffix)[index]? := by
  have erased := congrArg (fun log : OrderedRawQueryLog => log[index]?)
    (eraseIdx_pivot_append pre suffix pivot)
  rw [List.getElem?_eraseIdx] at erased
  by_cases before : index < pre.length
  · simpa [liftErasedIndex, before] using erased
  · simpa [liftErasedIndex, before] using erased

/-- A successful C1 node exposes its exact typed outer preimage and digest. -/
theorem extractC1Subtree_success_outer_exact
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (height : Nat) (expectedDigest : Digest208)
    (queryIndex : Nat) (leaves : List C1Leaf)
    (success : extractC1Subtree truncateSha256 log height expectedDigest
      queryIndex = .leaves leaves) :
    ∃ input, log[queryIndex]? = some input ∧
      truncateSha256 input = expectedDigest ∧
      parseTypedPreimage input ≠ none := by
  obtain ⟨input, inputExact, typed⟩ :=
    extractC1Subtree_success_outer_typed truncateSha256 log height
      expectedDigest queryIndex leaves success
  have digestExact : truncateSha256 input = expectedDigest := by
    cases height <;> simp only [extractC1Subtree] at success
    all_goals rw [inputExact] at success
    all_goals
      by_cases exact : truncateSha256 input = expectedDigest
      · exact exact
      · simp [exact] at success
  exact ⟨input, inputExact, digestExact, typed⟩

/-- A successful C2 node exposes its exact typed outer preimage and digest. -/
theorem extractC2Subtree_success_outer_exact
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (height : Nat) (expectedDigest : Digest208)
    (queryIndex : Nat) (leaves : List C2Leaf)
    (success : extractC2Subtree truncateSha256 log height expectedDigest
      queryIndex = .leaves leaves) :
    ∃ input, log[queryIndex]? = some input ∧
      truncateSha256 input = expectedDigest ∧
      parseTypedPreimage input ≠ none := by
  obtain ⟨input, inputExact, typed⟩ :=
    extractC2Subtree_success_outer_typed truncateSha256 log height
      expectedDigest queryIndex leaves success
  have digestExact : truncateSha256 input = expectedDigest := by
    cases height <;> simp only [extractC2Subtree] at success
    all_goals rw [inputExact] at success
    all_goals
      by_cases exact : truncateSha256 input = expectedDigest
      · exact exact
      · simp [exact] at success
  exact ⟨input, inputExact, digestExact, typed⟩

/-- `resolveFirstAux` is equivariant under a uniform change of its absolute
index offset. -/
theorem resolveFirstAux_offset_add
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208) :
    ∀ (log : OrderedRawQueryLog) (offset delta : Nat),
      resolveFirstAux truncateSha256 target (offset + delta) log =
        (resolveFirstAux truncateSha256 target offset log).map
          (fun index => index + delta) := by
  intro log
  induction log with
  | nil => intro offset delta; simp [resolveFirstAux]
  | cons head tail ih =>
      intro offset delta
      by_cases hit : truncateSha256 head = target
      · simp [resolveFirstAux, hit, Nat.add_comm]
      · rw [resolveFirstAux_cons_miss truncateSha256 target (offset + delta)
          head tail hit]
        rw [resolveFirstAux_cons_miss truncateSha256 target offset head tail hit]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (offset + 1) delta

/-- Removing one query which misses the target preserves `resolveFirstAux`,
with the unique expected index shift after the pivot. -/
theorem resolveFirstAux_erase_miss
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208) :
    ∀ (offset : Nat) (pre suffix : OrderedRawQueryLog)
      (pivot : RawHashInput),
      truncateSha256 pivot ≠ target →
      resolveFirstAux truncateSha256 target offset
          (pre ++ pivot :: suffix) =
        (resolveFirstAux truncateSha256 target offset (pre ++ suffix)).map
          (liftErasedIndex (offset + pre.length)) := by
  intro offset pre
  induction pre generalizing offset with
  | nil =>
      intro suffix pivot miss
      simp only [List.nil_append, List.length_nil, Nat.add_zero]
      rw [resolveFirstAux_cons_miss truncateSha256 target offset pivot suffix
        miss]
      rw [resolveFirstAux_offset_add truncateSha256 target suffix offset 1]
      cases resolved : resolveFirstAux truncateSha256 target offset suffix with
      | none => simp
      | some index =>
          have bound := resolveFirstAux_some_bounds truncateSha256 target offset
            suffix index resolved
          simp [liftErasedIndex]
          omega
  | cons head tail ih =>
      intro suffix pivot miss
      simp only [List.cons_append, List.length_cons]
      by_cases hit : truncateSha256 head = target
      · simp [resolveFirstAux, hit, liftErasedIndex]
      · rw [resolveFirstAux_cons_miss truncateSha256 target offset head
          (tail ++ pivot :: suffix) hit]
        rw [resolveFirstAux_cons_miss truncateSha256 target offset head
          (tail ++ suffix) hit]
        simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using ih (offset + 1) suffix pivot miss

/-- Root-index form of the erasure theorem. -/
theorem resolveFirst_erase_miss
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208)
    (pre suffix : OrderedRawQueryLog) (pivot : RawHashInput)
    (miss : truncateSha256 pivot ≠ target) :
    resolveFirst truncateSha256 target (pre ++ pivot :: suffix) =
      (resolveFirst truncateSha256 target (pre ++ suffix)).map
        (liftErasedIndex pre.length) := by
  simpa [resolveFirst] using resolveFirstAux_erase_miss truncateSha256 target
    0 pre suffix pivot miss

/-- The index embedding across one erased pivot is strictly monotone. -/
theorem liftErasedIndex_strictMono (pivot : Nat) :
    StrictMono (liftErasedIndex pivot) := by
  intro left right less
  unfold liftErasedIndex
  split <;> split <;> omega

/-- Hence the embedding reflects strict order as well as preserving it. -/
theorem liftErasedIndex_lt_iff (pivot left right : Nat) :
    liftErasedIndex pivot left < liftErasedIndex pivot right ↔ left < right := by
  constructor
  · intro lifted
    by_contra notLess
    have reverse : right ≤ left := Nat.le_of_not_gt notLess
    have monotone := (liftErasedIndex_strictMono pivot).monotone reverse
    omega
  · intro less
    exact liftErasedIndex_strictMono pivot less

/-- Concrete successful-root form of `resolveFirst_erase_miss`. -/
theorem resolveFirst_erase_miss_some
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208)
    (pre suffix : OrderedRawQueryLog) (pivot : RawHashInput) (index : Nat)
    (miss : truncateSha256 pivot ≠ target)
    (resolved : resolveFirst truncateSha256 target
      (pre ++ pivot :: suffix) = some index)
    (notPivot : index ≠ pre.length) :
    resolveFirst truncateSha256 target (pre ++ suffix) =
      some (lowerErasedIndex pre.length index) := by
  have transported := resolveFirst_erase_miss truncateSha256 target pre suffix
    pivot miss
  rw [resolved] at transported
  cases shortResolved : resolveFirst truncateSha256 target (pre ++ suffix) with
  | none => simp [shortResolved] at transported
  | some shortIndex =>
      have liftedExact : liftErasedIndex pre.length shortIndex = index := by
        simpa [shortResolved] using transported.symm
      have targetLifted : liftErasedIndex pre.length
          (lowerErasedIndex pre.length index) = index :=
        liftErasedIndex_lowerErasedIndex_of_ne pre.length index notPivot
      have shortExact : shortIndex = lowerErasedIndex pre.length index :=
        (liftErasedIndex_strictMono pre.length).injective
          (liftedExact.trans targetLifted.symm)
      simpa [shortExact] using shortResolved

/-- If a child is an earlier reference in the original log, erasing one
target-missing query preserves the same earlier edge after transporting both
absolute indices.  The proof resolves the child on the complete log first;
this avoids any assumption about whether the erased query lies before or
after the parent. -/
theorem classifyReference_erase_miss_earlier
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208)
    (pre suffix : OrderedRawQueryLog) (pivot : RawHashInput)
    (parentIndex childIndex : Nat)
    (parentBound : parentIndex < (pre ++ suffix).length)
    (miss : truncateSha256 pivot ≠ target)
    (earlier : classifyReference truncateSha256 target
      (liftErasedIndex pre.length parentIndex) (pre ++ pivot :: suffix) =
        .earlier (liftErasedIndex pre.length childIndex)) :
    classifyReference truncateSha256 target parentIndex (pre ++ suffix) =
      .earlier childIndex := by
  have fullChildBefore :
      liftErasedIndex pre.length childIndex <
        liftErasedIndex pre.length parentIndex :=
    earlier_index_lt_parent truncateSha256 target
      (liftErasedIndex pre.length parentIndex)
      (liftErasedIndex pre.length childIndex) (pre ++ pivot :: suffix) earlier
  have childBefore : childIndex < parentIndex :=
    (liftErasedIndex_lt_iff pre.length childIndex parentIndex).mp
      fullChildBefore
  have fullPrefixResolved : resolveFirstAux truncateSha256 target 0
      (List.take (liftErasedIndex pre.length parentIndex)
        (pre ++ pivot :: suffix)) =
        some (liftErasedIndex pre.length childIndex) := by
    unfold classifyReference at earlier
    generalize resolvedExact : resolveFirstAux truncateSha256 target 0
      (List.take (liftErasedIndex pre.length parentIndex)
        (pre ++ pivot :: suffix)) = resolved at earlier
    cases resolved with
    | none =>
        cases forward : resolveFirstAux truncateSha256 target
            (liftErasedIndex pre.length parentIndex)
            (List.drop (liftErasedIndex pre.length parentIndex)
              (pre ++ pivot :: suffix)) <;> simp [forward] at earlier
    | some index =>
        simpa using earlier
  have fullResolved : resolveFirst truncateSha256 target
      (pre ++ pivot :: suffix) =
        some (liftErasedIndex pre.length childIndex) := by
    have appended := resolveFirstAux_append_of_some truncateSha256 target 0
      (List.take (liftErasedIndex pre.length parentIndex)
        (pre ++ pivot :: suffix))
      (List.drop (liftErasedIndex pre.length parentIndex)
        (pre ++ pivot :: suffix))
      (liftErasedIndex pre.length childIndex) fullPrefixResolved
    simpa [resolveFirst, List.take_append_drop] using appended
  have erasedResolvedMap := resolveFirst_erase_miss truncateSha256 target pre
    suffix pivot miss
  rw [fullResolved] at erasedResolvedMap
  cases shortResolved : resolveFirst truncateSha256 target (pre ++ suffix) with
  | none => simp [shortResolved] at erasedResolvedMap
  | some shortIndex =>
      have liftedExact : liftErasedIndex pre.length shortIndex =
          liftErasedIndex pre.length childIndex := by
        simpa [shortResolved] using erasedResolvedMap.symm
      have shortIndexExact : shortIndex = childIndex :=
        (liftErasedIndex_strictMono pre.length).injective liftedExact
      subst shortIndex
      have prefixLength : (List.take parentIndex (pre ++ suffix)).length =
          parentIndex := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt parentBound)]
      have shortPrefixResolved : resolveFirstAux truncateSha256 target 0
          (List.take parentIndex (pre ++ suffix)) = some childIndex := by
        apply resolveFirstAux_prefix_of_append_some truncateSha256 target 0
          (List.take parentIndex (pre ++ suffix))
          (List.drop parentIndex (pre ++ suffix)) childIndex
        · simpa [resolveFirst, List.take_append_drop] using shortResolved
        · rw [prefixLength]
          simpa using childBefore
      unfold classifyReference
      rw [shortPrefixResolved]

/-! ## Recursive subtree transport -/

/-- Successful C1 traversal survives erasure of one untyped, collision-free
query at an arbitrary chronological position. -/
theorem extractC1Subtree_success_erase_untyped
    (truncateSha256 : RawHashInput → Digest208)
    (pre suffix : OrderedRawQueryLog) (pivot : RawHashInput)
    (noCollision : hasRawTruncatedCollision truncateSha256
      (pre ++ pivot :: suffix) = false)
    (pivotUntyped : parseTypedPreimage pivot = none) :
    ∀ (height : Nat) (expectedDigest : Digest208) (queryIndex : Nat)
      (leaves : List C1Leaf),
      queryIndex < (pre ++ suffix).length →
      extractC1Subtree truncateSha256 (pre ++ pivot :: suffix) height
          expectedDigest (liftErasedIndex pre.length queryIndex) =
        .leaves leaves →
      extractC1Subtree truncateSha256 (pre ++ suffix) height expectedDigest
          queryIndex = .leaves leaves := by
  intro height
  induction height with
  | zero =>
      intro expectedDigest queryIndex leaves queryBound success
      simp only [extractC1Subtree] at success ⊢
      rw [getElem?_erase_pivot_lift pre suffix pivot queryIndex] at success
      exact success
  | succ height ih =>
      intro expectedDigest queryIndex leaves queryBound success
      simp only [extractC1Subtree] at success ⊢
      rw [getElem?_erase_pivot_lift pre suffix pivot queryIndex] at success
      generalize inputExact : (pre ++ suffix)[queryIndex]? = inputOption
        at success ⊢
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
                      if child = defaultC1SubtreeDigest truncateSha256 height then
                        SubtreeResult.leaves
                          (List.replicate (2 ^ height) defaultC1Leaf)
                      else
                        match classifyReference truncateSha256 child
                            (liftErasedIndex pre.length queryIndex)
                            (pre ++ pivot :: suffix) with
                        | .earlier childIndex =>
                            extractC1Subtree truncateSha256
                              (pre ++ pivot :: suffix) height child childIndex
                        | .forward _ => .failure .forwardReference
                        | .missing => .failure .missingPreimageQuery
                    let shortChild := fun child =>
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
                    have childSuccess : ∀ child childLeaves,
                        fullChild child = .leaves childLeaves →
                          shortChild child = .leaves childLeaves := by
                      intro child childLeaves childRun
                      by_cases isDefault : child =
                          defaultC1SubtreeDigest truncateSha256 height
                      · simpa [fullChild, shortChild, isDefault] using childRun
                      · cases referenceExact : classifyReference truncateSha256
                            child (liftErasedIndex pre.length queryIndex)
                            (pre ++ pivot :: suffix) with
                        | earlier fullChildIndex =>
                            have fullRun : extractC1Subtree truncateSha256
                                (pre ++ pivot :: suffix) height child
                                  fullChildIndex = .leaves childLeaves := by
                              simpa [fullChild, isDefault, referenceExact] using
                                childRun
                            obtain ⟨childInput, childInputExact,
                                childDigestExact, childTyped⟩ :=
                              extractC1Subtree_success_outer_exact truncateSha256
                                (pre ++ pivot :: suffix) height child
                                  fullChildIndex childLeaves fullRun
                            have childMem : childInput ∈
                                pre ++ pivot :: suffix :=
                              List.mem_of_getElem? childInputExact
                            have childNotPivot : fullChildIndex ≠ pre.length := by
                              intro indexExact
                              have pivotAt :
                                  (pre ++ pivot :: suffix)[pre.length]? =
                                    some pivot := by simp
                              have inputsExact : childInput = pivot := by
                                apply Option.some.inj
                                exact childInputExact.symm.trans (by
                                  simpa [indexExact] using pivotAt)
                              subst childInput
                              exact childTyped pivotUntyped
                            let reducedIndex := lowerErasedIndex pre.length
                              fullChildIndex
                            have liftedIndex : liftErasedIndex pre.length
                                reducedIndex = fullChildIndex :=
                              liftErasedIndex_lowerErasedIndex_of_ne pre.length
                                fullChildIndex childNotPivot
                            have fullBefore := earlier_index_lt_parent
                              truncateSha256 child
                                (liftErasedIndex pre.length queryIndex)
                                fullChildIndex (pre ++ pivot :: suffix)
                                  referenceExact
                            have reducedBefore : reducedIndex < queryIndex := by
                              rw [← liftErasedIndex_lt_iff pre.length]
                              simpa [liftedIndex] using fullBefore
                            have reducedBound : reducedIndex <
                                (pre ++ suffix).length :=
                              lt_trans reducedBefore queryBound
                            have pivotMiss : truncateSha256 pivot ≠ child := by
                              intro pivotExact
                              exact (untyped_pivot_digest_ne_typed_member
                                truncateSha256 pre suffix pivot childInput
                                noCollision pivotUntyped childMem childTyped)
                                  (pivotExact.trans childDigestExact.symm)
                            have shortReference :=
                              classifyReference_erase_miss_earlier
                                truncateSha256 child pre suffix pivot queryIndex
                                  reducedIndex queryBound pivotMiss (by
                                    simpa [liftedIndex] using referenceExact)
                            have shortRun := ih child reducedIndex childLeaves
                              reducedBound (by simpa [liftedIndex] using fullRun)
                            simpa [shortChild, isDefault, shortReference] using
                              shortRun
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
                    change (match shortChild left with
                      | .failure reason => SubtreeResult.failure reason
                      | .leaves leftLeaves =>
                          match shortChild right with
                          | .failure reason => SubtreeResult.failure reason
                          | .leaves rightLeaves =>
                              SubtreeResult.leaves
                                (leftLeaves ++ rightLeaves)) =
                        SubtreeResult.leaves leaves
                    cases leftRun : fullChild left with
                    | failure reason => simp [leftRun] at success
                    | leaves leftLeaves =>
                        have leftShort := childSuccess left leftLeaves leftRun
                        cases rightRun : fullChild right with
                        | failure reason => simp [leftRun, rightRun] at success
                        | leaves rightLeaves =>
                            have rightShort := childSuccess right rightLeaves
                              rightRun
                            have leavesExact : leftLeaves ++ rightLeaves =
                                leaves := by
                              simpa [leftRun, rightRun] using success
                            rw [leftShort, rightShort]
                            exact congrArg SubtreeResult.leaves leavesExact
          · simp only [digestExact, ↓reduceIte] at success ⊢
            simp at success


/-- Successful C2 traversal survives erasure of one untyped, collision-free
query at an arbitrary chronological position. -/
theorem extractC2Subtree_success_erase_untyped
    (truncateSha256 : RawHashInput → Digest208)
    (pre suffix : OrderedRawQueryLog) (pivot : RawHashInput)
    (noCollision : hasRawTruncatedCollision truncateSha256
      (pre ++ pivot :: suffix) = false)
    (pivotUntyped : parseTypedPreimage pivot = none) :
    ∀ (height : Nat) (expectedDigest : Digest208) (queryIndex : Nat)
      (leaves : List C2Leaf),
      queryIndex < (pre ++ suffix).length →
      extractC2Subtree truncateSha256 (pre ++ pivot :: suffix) height
          expectedDigest (liftErasedIndex pre.length queryIndex) =
        .leaves leaves →
      extractC2Subtree truncateSha256 (pre ++ suffix) height expectedDigest
          queryIndex = .leaves leaves := by
  intro height
  induction height with
  | zero =>
      intro expectedDigest queryIndex leaves queryBound success
      simp only [extractC2Subtree] at success ⊢
      rw [getElem?_erase_pivot_lift pre suffix pivot queryIndex] at success
      exact success
  | succ height ih =>
      intro expectedDigest queryIndex leaves queryBound success
      simp only [extractC2Subtree] at success ⊢
      rw [getElem?_erase_pivot_lift pre suffix pivot queryIndex] at success
      generalize inputExact : (pre ++ suffix)[queryIndex]? = inputOption
        at success ⊢
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
                        match classifyReference truncateSha256 child
                            (liftErasedIndex pre.length queryIndex)
                            (pre ++ pivot :: suffix) with
                        | .earlier childIndex =>
                            extractC2Subtree truncateSha256
                              (pre ++ pivot :: suffix) height child childIndex
                        | .forward _ => .failure .forwardReference
                        | .missing => .failure .missingPreimageQuery
                    let shortChild := fun child =>
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
                    have childSuccess : ∀ child childLeaves,
                        fullChild child = .leaves childLeaves →
                          shortChild child = .leaves childLeaves := by
                      intro child childLeaves childRun
                      by_cases isDefault : child =
                          defaultC2SubtreeDigest truncateSha256 height
                      · simpa [fullChild, shortChild, isDefault] using childRun
                      · cases referenceExact : classifyReference truncateSha256
                            child (liftErasedIndex pre.length queryIndex)
                            (pre ++ pivot :: suffix) with
                        | earlier fullChildIndex =>
                            have fullRun : extractC2Subtree truncateSha256
                                (pre ++ pivot :: suffix) height child
                                  fullChildIndex = .leaves childLeaves := by
                              simpa [fullChild, isDefault, referenceExact] using
                                childRun
                            obtain ⟨childInput, childInputExact,
                                childDigestExact, childTyped⟩ :=
                              extractC2Subtree_success_outer_exact truncateSha256
                                (pre ++ pivot :: suffix) height child
                                  fullChildIndex childLeaves fullRun
                            have childMem : childInput ∈
                                pre ++ pivot :: suffix :=
                              List.mem_of_getElem? childInputExact
                            have childNotPivot : fullChildIndex ≠ pre.length := by
                              intro indexExact
                              have pivotAt :
                                  (pre ++ pivot :: suffix)[pre.length]? =
                                    some pivot := by simp
                              have inputsExact : childInput = pivot := by
                                apply Option.some.inj
                                exact childInputExact.symm.trans (by
                                  simpa [indexExact] using pivotAt)
                              subst childInput
                              exact childTyped pivotUntyped
                            let reducedIndex := lowerErasedIndex pre.length
                              fullChildIndex
                            have liftedIndex : liftErasedIndex pre.length
                                reducedIndex = fullChildIndex :=
                              liftErasedIndex_lowerErasedIndex_of_ne pre.length
                                fullChildIndex childNotPivot
                            have fullBefore := earlier_index_lt_parent
                              truncateSha256 child
                                (liftErasedIndex pre.length queryIndex)
                                fullChildIndex (pre ++ pivot :: suffix)
                                  referenceExact
                            have reducedBefore : reducedIndex < queryIndex := by
                              rw [← liftErasedIndex_lt_iff pre.length]
                              simpa [liftedIndex] using fullBefore
                            have reducedBound : reducedIndex <
                                (pre ++ suffix).length :=
                              lt_trans reducedBefore queryBound
                            have pivotMiss : truncateSha256 pivot ≠ child := by
                              intro pivotExact
                              exact (untyped_pivot_digest_ne_typed_member
                                truncateSha256 pre suffix pivot childInput
                                noCollision pivotUntyped childMem childTyped)
                                  (pivotExact.trans childDigestExact.symm)
                            have shortReference :=
                              classifyReference_erase_miss_earlier
                                truncateSha256 child pre suffix pivot queryIndex
                                  reducedIndex queryBound pivotMiss (by
                                    simpa [liftedIndex] using referenceExact)
                            have shortRun := ih child reducedIndex childLeaves
                              reducedBound (by simpa [liftedIndex] using fullRun)
                            simpa [shortChild, isDefault, shortReference] using
                              shortRun
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
                    change (match shortChild left with
                      | .failure reason => SubtreeResult.failure reason
                      | .leaves leftLeaves =>
                          match shortChild right with
                          | .failure reason => SubtreeResult.failure reason
                          | .leaves rightLeaves =>
                              SubtreeResult.leaves
                                (leftLeaves ++ rightLeaves)) =
                        SubtreeResult.leaves leaves
                    cases leftRun : fullChild left with
                    | failure reason => simp [leftRun] at success
                    | leaves leftLeaves =>
                        have leftShort := childSuccess left leftLeaves leftRun
                        cases rightRun : fullChild right with
                        | failure reason => simp [leftRun, rightRun] at success
                        | leaves rightLeaves =>
                            have rightShort := childSuccess right rightLeaves
                              rightRun
                            have leavesExact : leftLeaves ++ rightLeaves =
                                leaves := by
                              simpa [leftRun, rightRun] using success
                            rw [leftShort, rightShort]
                            exact congrArg SubtreeResult.leaves leavesExact
          · simp only [digestExact, ↓reduceIte] at success ⊢
            simp at success

/-! ## Complete two-tree transport -/

/-- A successful complete two-tree extraction survives erasure of one
untyped, collision-free query at an arbitrary chronological position. -/
theorem extractCompleteWords_success_erase_untyped_raw
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (pre suffix : OrderedRawQueryLog) (pivot : RawHashInput)
    (words : ExtractedWords)
    (noCollision : hasRawTruncatedCollision truncateSha256
      (pre ++ pivot :: suffix) = false)
    (pivotUntyped : parseTypedPreimage pivot = none)
    (success : extractCompleteWords truncateSha256 roots
      (pre ++ pivot :: suffix) = .words words) :
    extractCompleteWords truncateSha256 roots (pre ++ suffix) =
      .words words := by
  obtain ⟨c1Index, c2Index, c1Resolved, c2Resolved, c1Run, c2Run⟩ :=
    extractCompleteWords_success_yields_root_queries truncateSha256 roots
      (pre ++ pivot :: suffix) words success
  obtain ⟨c1Input, c1InputExact, c1DigestExact, c1Typed⟩ :=
    extractC1Subtree_success_outer_exact truncateSha256
      (pre ++ pivot :: suffix) treeDepth roots.c1 c1Index words.c1 c1Run
  obtain ⟨c2Input, c2InputExact, c2DigestExact, c2Typed⟩ :=
    extractC2Subtree_success_outer_exact truncateSha256
      (pre ++ pivot :: suffix) treeDepth roots.c2 c2Index words.c2 c2Run
  have c1Mem : c1Input ∈ pre ++ pivot :: suffix :=
    List.mem_of_getElem? c1InputExact
  have c2Mem : c2Input ∈ pre ++ pivot :: suffix :=
    List.mem_of_getElem? c2InputExact
  have c1NotPivot : c1Index ≠ pre.length := by
    intro indexExact
    have pivotAt : (pre ++ pivot :: suffix)[pre.length]? = some pivot := by simp
    have inputExact : c1Input = pivot := by
      apply Option.some.inj
      exact c1InputExact.symm.trans (by simpa [indexExact] using pivotAt)
    subst c1Input
    exact c1Typed pivotUntyped
  have c2NotPivot : c2Index ≠ pre.length := by
    intro indexExact
    have pivotAt : (pre ++ pivot :: suffix)[pre.length]? = some pivot := by simp
    have inputExact : c2Input = pivot := by
      apply Option.some.inj
      exact c2InputExact.symm.trans (by simpa [indexExact] using pivotAt)
    subst c2Input
    exact c2Typed pivotUntyped
  have c1Miss : truncateSha256 pivot ≠ roots.c1 :=
    untyped_pivot_ne_typed_target truncateSha256 pre suffix pivot c1Input
      roots.c1 noCollision pivotUntyped c1Mem c1Typed c1DigestExact
  have c2Miss : truncateSha256 pivot ≠ roots.c2 :=
    untyped_pivot_ne_typed_target truncateSha256 pre suffix pivot c2Input
      roots.c2 noCollision pivotUntyped c2Mem c2Typed c2DigestExact
  let c1Short := lowerErasedIndex pre.length c1Index
  let c2Short := lowerErasedIndex pre.length c2Index
  have c1ResolvedShort : resolveFirst truncateSha256 roots.c1
      (pre ++ suffix) = some c1Short :=
    resolveFirst_erase_miss_some truncateSha256 roots.c1 pre suffix pivot
      c1Index c1Miss c1Resolved c1NotPivot
  have c2ResolvedShort : resolveFirst truncateSha256 roots.c2
      (pre ++ suffix) = some c2Short :=
    resolveFirst_erase_miss_some truncateSha256 roots.c2 pre suffix pivot
      c2Index c2Miss c2Resolved c2NotPivot
  have c1Bound : c1Short < (pre ++ suffix).length := by
    simpa using (resolveFirstAux_some_bounds truncateSha256 roots.c1 0
      (pre ++ suffix) c1Short (by simpa [resolveFirst] using
        c1ResolvedShort)).2
  have c2Bound : c2Short < (pre ++ suffix).length := by
    simpa using (resolveFirstAux_some_bounds truncateSha256 roots.c2 0
      (pre ++ suffix) c2Short (by simpa [resolveFirst] using
        c2ResolvedShort)).2
  have c1Lifted : liftErasedIndex pre.length c1Short = c1Index :=
    liftErasedIndex_lowerErasedIndex_of_ne pre.length c1Index c1NotPivot
  have c2Lifted : liftErasedIndex pre.length c2Short = c2Index :=
    liftErasedIndex_lowerErasedIndex_of_ne pre.length c2Index c2NotPivot
  have c1RunShort := extractC1Subtree_success_erase_untyped truncateSha256 pre
    suffix pivot noCollision pivotUntyped treeDepth roots.c1 c1Short words.c1
      c1Bound (by simpa [c1Lifted] using c1Run)
  have c2RunShort := extractC2Subtree_success_erase_untyped truncateSha256 pre
    suffix pivot noCollision pivotUntyped treeDepth roots.c2 c2Short words.c2
      c2Bound (by simpa [c2Lifted] using c2Run)
  simp [extractCompleteWords, c1ResolvedShort, c2ResolvedShort, c1RunShort,
    c2RunShort]

/-! ## Iterated erasure -/

/-- Keep exactly the inputs which parse under the Merkle query grammar. -/
def retainTypedMerkleQueries (log : OrderedRawQueryLog) : OrderedRawQueryLog :=
  log.filter fun input => decide (parseTypedPreimage input ≠ none)

/-- Inputs outside the three frozen Merkle wire lengths are untyped. -/
theorem parseTypedPreimage_eq_none_of_length
    (input : RawHashInput)
    (notC1 : input.length ≠ 437) (notC2 : input.length ≠ 220)
    (notNode : input.length ≠ 53) :
    parseTypedPreimage input = none := by
  simp [parseTypedPreimage, notC1, notC2, notNode]

/-- Collision-freedom is inherited when one query is erased. -/
theorem no_collision_after_erasing_one
    (truncateSha256 : RawHashInput → Digest208)
    (pre suffix : OrderedRawQueryLog) (pivot : RawHashInput)
    (noCollision : hasRawTruncatedCollision truncateSha256
      (pre ++ pivot :: suffix) = false) :
    hasRawTruncatedCollision truncateSha256 (pre ++ suffix) = false := by
  rw [no_raw_truncated_collision_iff] at noCollision ⊢
  intro shortenedCollision
  apply noCollision
  rcases shortenedCollision with
    ⟨left, leftMem, right, rightMem, distinct, digestExact⟩
  have liftMember : ∀ input, input ∈ pre ++ suffix →
      input ∈ pre ++ pivot :: suffix := by
    intro input member
    simp only [List.mem_append, List.mem_cons] at member ⊢
    rcases member with member | member
    · exact Or.inl member
    · exact Or.inr (Or.inr member)
  exact ⟨left, liftMember left leftMem, right, liftMember right rightMem,
    distinct, digestExact⟩

/-- The collision universe contains the shared log, so the production
collision gate implies collision-freedom on that log itself. -/
theorem no_shared_collision_of_no_universe_collision
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog)
    (noCollision : hasRawTruncatedCollision truncateSha256
      (collisionUniverse truncateSha256 log) = false) :
    hasRawTruncatedCollision truncateSha256 log = false := by
  rw [no_raw_truncated_collision_iff] at noCollision ⊢
  intro sharedCollision
  apply noCollision
  rcases sharedCollision with
    ⟨left, leftMem, right, rightMem, distinct, digestExact⟩
  exact ⟨left, shared_log_mem_collisionUniverse truncateSha256 log leftMem,
    right, shared_log_mem_collisionUniverse truncateSha256 log rightMem,
    distinct, digestExact⟩

/-- Starting after an already retained prefix, erase every remaining untyped
query while preserving a successful complete two-tree extraction. -/
theorem extractCompleteWords_success_retain_typed_aux
    (truncateSha256 : RawHashInput → Digest208) (roots : Roots) :
    ∀ (scan kept : OrderedRawQueryLog) (words : ExtractedWords),
      hasRawTruncatedCollision truncateSha256 (kept ++ scan) = false →
      extractCompleteWords truncateSha256 roots (kept ++ scan) = .words words →
      extractCompleteWords truncateSha256 roots
        (kept ++ retainTypedMerkleQueries scan) = .words words := by
  intro scan
  induction scan with
  | nil =>
      intro kept words noCollision success
      simpa [retainTypedMerkleQueries] using success
  | cons head tail ih =>
      intro kept words noCollision success
      by_cases untyped : parseTypedPreimage head = none
      · have erased := extractCompleteWords_success_erase_untyped_raw
          truncateSha256 roots kept tail head words noCollision untyped success
        have erasedCollision := no_collision_after_erasing_one truncateSha256
          kept tail head noCollision
        have retained := ih kept words erasedCollision erased
        simpa [retainTypedMerkleQueries, untyped] using retained
      · have retained := ih (kept ++ [head]) words (by
            simpa [List.append_assoc] using noCollision) (by
            simpa [List.append_assoc] using success)
        simpa [retainTypedMerkleQueries, untyped, List.append_assoc] using
          retained

/-- Erasing all non-Merkle transcript queries preserves the exact complete
two-tree candidate. -/
theorem extractCompleteWords_success_retain_typed
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (log : OrderedRawQueryLog) (words : ExtractedWords)
    (noCollision : hasRawTruncatedCollision truncateSha256 log = false)
    (success : extractCompleteWords truncateSha256 roots log = .words words) :
    extractCompleteWords truncateSha256 roots (retainTypedMerkleQueries log) =
      .words words := by
  simpa using extractCompleteWords_success_retain_typed_aux truncateSha256
    roots log [] words (by simpa using noCollision) (by simpa using success)

/-- Every successful production extraction fixes its returned complete words
already on the retained typed-Merkle subsequence.  All transcript-only SHA
queries have been removed. -/
theorem extractV7Words_success_yields_typed_complete
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (orderedQueries : OrderedRawQueryLog) (words : ExtractedWords)
    (success : extractV7Words truncateSha256 roots proof orderedQueries =
      .words words) :
    extractCompleteWords truncateSha256 roots
      (retainTypedMerkleQueries (deduplicateFirst orderedQueries)) =
        .words words := by
  by_cases collision : hasRawTruncatedCollision truncateSha256
      (collisionUniverse truncateSha256 (deduplicateFirst orderedQueries))
  · simp [extractV7Words, collision] at success
  · cases graph : extractCompleteWords truncateSha256 roots
        (deduplicateFirst orderedQueries) with
    | failure reason => simp [extractV7Words, collision, graph] at success
    | words candidate =>
        have finished : finishExtraction truncateSha256 roots proof candidate =
            .words words := by
          simpa [extractV7Words, collision, graph] using success
        have candidateExact := (finishExtraction_success_yields_match
          truncateSha256 roots proof candidate words finished).1
        subst candidate
        apply extractCompleteWords_success_retain_typed truncateSha256 roots
          (deduplicateFirst orderedQueries) words
        · exact no_shared_collision_of_no_universe_collision truncateSha256
            (deduplicateFirst orderedQueries)
            (Bool.eq_false_of_not_eq_true collision)
        · exact graph

/-- A successful production extraction exposes the exact complete-tree graph
which produced its returned words, before supplied-opening projection. -/
theorem extractV7Words_success_yields_complete
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (orderedQueries : OrderedRawQueryLog) (words : ExtractedWords)
    (success : extractV7Words truncateSha256 roots proof orderedQueries =
      .words words) :
    extractCompleteWords truncateSha256 roots
      (deduplicateFirst orderedQueries) = .words words := by
  by_cases collision : hasRawTruncatedCollision truncateSha256
      (collisionUniverse truncateSha256 (deduplicateFirst orderedQueries))
  · simp [extractV7Words, collision] at success
  · cases graph : extractCompleteWords truncateSha256 roots
        (deduplicateFirst orderedQueries) with
    | failure reason => simp [extractV7Words, collision, graph] at success
    | words candidate =>
        have finished : finishExtraction truncateSha256 roots proof candidate =
            .words words := by
          simpa [extractV7Words, collision, graph] using success
        have candidateExact := (finishExtraction_success_yields_match
          truncateSha256 roots proof candidate words finished).1
        simpa [candidateExact] using graph

#print axioms eraseIdx_pivot_append
#print axioms truncate_injective_on_log_of_no_collision
#print axioms untyped_pivot_digest_ne_typed_member
#print axioms untyped_pivot_ne_typed_target
#print axioms resolveFirstAux_offset_add
#print axioms resolveFirstAux_erase_miss
#print axioms resolveFirst_erase_miss
#print axioms resolveFirst_erase_miss_some
#print axioms liftErasedIndex_strictMono
#print axioms liftErasedIndex_lt_iff
#print axioms lowerErasedIndex_liftErasedIndex
#print axioms liftErasedIndex_lowerErasedIndex_of_ne
#print axioms getElem?_erase_pivot_lift
#print axioms extractC1Subtree_success_outer_exact
#print axioms extractC2Subtree_success_outer_exact
#print axioms classifyReference_erase_miss_earlier
#print axioms extractC1Subtree_success_erase_untyped
#print axioms extractC2Subtree_success_erase_untyped
#print axioms extractCompleteWords_success_erase_untyped_raw
#print axioms retainTypedMerkleQueries
#print axioms parseTypedPreimage_eq_none_of_length
#print axioms no_collision_after_erasing_one
#print axioms no_shared_collision_of_no_universe_collision
#print axioms extractCompleteWords_success_retain_typed_aux
#print axioms extractCompleteWords_success_retain_typed
#print axioms extractV7Words_success_yields_typed_complete
#print axioms extractV7Words_success_yields_complete

end AspisPool.V7MerkleUntypedErasureStability
