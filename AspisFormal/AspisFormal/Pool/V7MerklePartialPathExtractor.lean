import AspisFormal.Pool.V7MerkleAcceptedOpeningProjection

/-!
# Prefix-fixed partial Merkle-path extraction for Tag-73

The committed oracle used by the proximity argument must be fixed before the
query positions are sampled.  A malicious commitment need not expose every
off-path subtree preimage, so requiring a complete queried Merkle tree is too
strong.  This module instead follows one root-to-leaf path through the
pre-challenge query log.  Unresolved positions may be completed arbitrarily;
resolved positions carry an exact authentication path whose every raw hash
input was already present in that fixed log.

This is a deterministic layer.  The later ROM game must bound the event that
an accepted post-challenge opening reaches a path which was not resolvable in
the prefix, together with the shared 208-bit collision event.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisPool.V7MerklePartialPathExtractor

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisPool.V7MerkleAcceptedOpeningProjection
open AspisPool.V7MerkleCanonicalOpening

/-! ## Successful parser round trip -/

theorem parseTypedPreimage_success_reserializes
    (input : RawHashInput) (typed : TypedPreimage)
    (parsed : parseTypedPreimage input = some typed) :
    serialize typed = input := by
  unfold parseTypedPreimage at parsed
  by_cases c1Header : input.length = 437 ∧ input.take 2 = [0x10, 0x71]
  · rw [if_pos c1Header] at parsed
    have inputSplit : input = input.take 2 ++ input.drop 2 :=
      (List.take_append_drop 2 input).symm
    have tailLength : (input.drop 2).length = 435 := by
      rw [List.length_drop, c1Header.1]
    have valueLength : ((input.drop 2).take 403).length = 403 := by
      simp [List.length_take, tailLength]
    have saltLength : ((input.drop 2).drop 403).length = 32 := by
      rw [List.length_drop, tailLength]
    injection parsed with typedExact
    subst typed
    simp only [serialize]
    rw [fixedBytes_fixedOfListD_of_length _ valueLength,
      fixedBytes_fixedOfListD_of_length _ saltLength]
    change [0x10, 0x71] ++
        ((input.drop 2).take 403 ++ (input.drop 2).drop 403) = input
    calc
      _ = input.take 2 ++
          ((input.drop 2).take 403 ++ (input.drop 2).drop 403) := by
            rw [c1Header.2]
      _ = input.take 2 ++ input.drop 2 := by
            rw [List.take_append_drop]
      _ = input := List.take_append_drop 2 input
  · rw [if_neg c1Header] at parsed
    by_cases c2Header : input.length = 220 ∧ input.take 2 = [0x10, 0xf1]
    · rw [if_pos c2Header] at parsed
      have inputSplit : input = input.take 2 ++ input.drop 2 :=
        (List.take_append_drop 2 input).symm
      have tailLength : (input.drop 2).length = 218 := by
        rw [List.length_drop, c2Header.1]
      have valueLength : ((input.drop 2).take 186).length = 186 := by
        simp [List.length_take, tailLength]
      have saltLength : ((input.drop 2).drop 186).length = 32 := by
        rw [List.length_drop, tailLength]
      injection parsed with typedExact
      subst typed
      simp only [serialize]
      rw [fixedBytes_fixedOfListD_of_length _ valueLength,
        fixedBytes_fixedOfListD_of_length _ saltLength]
      change [0x10, 0xf1] ++
          ((input.drop 2).take 186 ++ (input.drop 2).drop 186) = input
      calc
        _ = input.take 2 ++
            ((input.drop 2).take 186 ++ (input.drop 2).drop 186) := by
              rw [c2Header.2]
        _ = input.take 2 ++ input.drop 2 := by
              rw [List.take_append_drop]
        _ = input := List.take_append_drop 2 input
    · rw [if_neg c2Header] at parsed
      by_cases nodeHeader : input.length = 53 ∧ input.take 1 = [0x11]
      · rw [if_pos nodeHeader] at parsed
        have inputSplit : input = input.take 1 ++ input.drop 1 :=
          (List.take_append_drop 1 input).symm
        have tailLength : (input.drop 1).length = 52 := by
          rw [List.length_drop, nodeHeader.1]
        have leftLength : ((input.drop 1).take 26).length = 26 := by
          simp only [List.length_take, List.length_drop]
          omega
        have rightLength : ((input.drop 1).drop 26).length = 26 := by
          simp only [List.length_drop]
          omega
        injection parsed with typedExact
        subst typed
        simp only [serialize]
        rw [fixedBytes_fixedOfListD_of_length _ leftLength,
          fixedBytes_fixedOfListD_of_length _ rightLength]
        change [0x11] ++
            ((input.drop 1).take 26 ++ (input.drop 1).drop 26) = input
        calc
          _ = input.take 1 ++
              ((input.drop 1).take 26 ++ (input.drop 1).drop 26) := by
                rw [nodeHeader.2]
          _ = input.take 1 ++ input.drop 1 := by
                rw [List.take_append_drop]
          _ = input := List.take_append_drop 1 input
      · rw [if_neg nodeHeader] at parsed
        contradiction

/-! ## Raw-prefix resolver -/

def resolveInput (truncateSha256 : RawHashInput → Digest208)
    (target : Digest208) (log : OrderedRawQueryLog) : Option RawHashInput :=
  log.find? (fun input => truncateSha256 input = target)

theorem resolveInput_success_digest
    (truncateSha256 : RawHashInput → Digest208)
    (target : Digest208) (log : OrderedRawQueryLog) (input : RawHashInput)
    (resolved : resolveInput truncateSha256 target log = some input) :
    truncateSha256 input = target := by
  unfold resolveInput at resolved
  have predicate : decide (truncateSha256 input = target) = true :=
    List.find?_some
      (p := fun candidate => decide (truncateSha256 candidate = target))
      resolved
  exact of_decide_eq_true predicate

theorem resolveInput_success_mem
    (truncateSha256 : RawHashInput → Digest208)
    (target : Digest208) (log : OrderedRawQueryLog) (input : RawHashInput)
    (resolved : resolveInput truncateSha256 target log = some input) :
    input ∈ log := by
  exact List.mem_of_find?_eq_some resolved

/-! ## One executable root-to-leaf traversal -/

structure ResolvedPath (Leaf : Type) (height : Nat) where
  leaf : Leaf
  /-- Bottom-up siblings, matching the deployed opening order. -/
  siblings : Fin height → Digest208

def appendTopSibling {Leaf : Type} {height : Nat}
    (path : ResolvedPath Leaf height) (top : Digest208) :
    ResolvedPath Leaf (height + 1) where
  leaf := path.leaf
  siblings := Fin.append path.siblings (fun _ : Fin 1 => top)

def parseC1Leaf (input : RawHashInput) : Option C1Leaf :=
  match parseTypedPreimage input with
  | some (.c1Leaf value salt) => some ⟨value, salt⟩
  | _ => none

def parseC2Leaf (input : RawHashInput) : Option C2Leaf :=
  match parseTypedPreimage input with
  | some (.c2Leaf value salt) => some ⟨value, salt⟩
  | _ => none

theorem parseC1Leaf_success_reserializes
    (input : RawHashInput) (leaf : C1Leaf)
    (parsed : parseC1Leaf input = some leaf) :
    serialize (.c1Leaf leaf.value leaf.salt) = input := by
  unfold parseC1Leaf at parsed
  cases typedEquation : parseTypedPreimage input with
  | none => simp [typedEquation] at parsed
  | some typed =>
      cases typed with
      | c1Leaf value salt =>
          simp only [typedEquation, Option.some.injEq] at parsed
          subst leaf
          exact parseTypedPreimage_success_reserializes input
            (.c1Leaf value salt) typedEquation
      | c2Leaf value salt => simp [typedEquation] at parsed
      | node left right => simp [typedEquation] at parsed

theorem parseC2Leaf_success_reserializes
    (input : RawHashInput) (leaf : C2Leaf)
    (parsed : parseC2Leaf input = some leaf) :
    serialize (.c2Leaf leaf.value leaf.salt) = input := by
  unfold parseC2Leaf at parsed
  cases typedEquation : parseTypedPreimage input with
  | none => simp [typedEquation] at parsed
  | some typed =>
      cases typed with
      | c1Leaf value salt => simp [typedEquation] at parsed
      | c2Leaf value salt =>
          simp only [typedEquation, Option.some.injEq] at parsed
          subst leaf
          exact parseTypedPreimage_success_reserializes input
            (.c2Leaf value salt) typedEquation
      | node left right => simp [typedEquation] at parsed

def resolvePath {Leaf : Type}
    (parseLeaf : RawHashInput → Option Leaf)
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) :
    (height : Nat) → Digest208 → Nat → Option (ResolvedPath Leaf height)
  | 0, target, _ => do
      let input ← resolveInput truncateSha256 target log
      let leaf ← parseLeaf input
      pure ⟨leaf, Fin.elim0⟩
  | height + 1, target, position => do
      let input ← resolveInput truncateSha256 target log
      match parseTypedPreimage input with
      | some (.node left right) =>
          if position.testBit height then
            return appendTopSibling
              (← resolvePath parseLeaf truncateSha256 log height right position)
              left
          else
            return appendTopSibling
              (← resolvePath parseLeaf truncateSha256 log height left position)
              right
      | _ => none

def resolveC1Path (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (root : Digest208) (position : Position) :
    Option (ResolvedPath C1Leaf treeDepth) :=
  resolvePath parseC1Leaf truncateSha256 log treeDepth root position.val

def resolveC2Path (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (root : Digest208) (position : Position) :
    Option (ResolvedPath C2Leaf treeDepth) :=
  resolvePath parseC2Leaf truncateSha256 log treeDepth root position.val

/-! ## First unresolved digest targets

This companion traversal returns the digest whose matching preimage is first
unavailable (or has the wrong grammar) while walking from the public root
toward one sampled leaf.  Unlike the opening trace, it is root-to-leaf: when
a parent is already resolved in the prover-final prefix, the next target is
the selected child digest stored in that prefix-fixed parent.
-/

def firstUnresolvedTarget {Leaf : Type}
    (parseLeaf : RawHashInput → Option Leaf)
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) :
    (height : Nat) → Digest208 → Nat → Option Digest208
  | 0, target, _ =>
      match resolveInput truncateSha256 target log with
      | none => some target
      | some input =>
          match parseLeaf input with
          | none => some target
          | some _ => none
  | height + 1, target, position =>
      match resolveInput truncateSha256 target log with
      | none => some target
      | some input =>
          match parseTypedPreimage input with
          | some (.node left right) =>
              if position.testBit height then
                firstUnresolvedTarget parseLeaf truncateSha256 log
                  height right position
              else
                firstUnresolvedTarget parseLeaf truncateSha256 log
                  height left position
          | _ => some target

def firstUnresolvedC1Target
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (root : Digest208) (position : Position) :
    Option Digest208 :=
  firstUnresolvedTarget parseC1Leaf truncateSha256 log treeDepth root
    position.val

def firstUnresolvedC2Target
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (root : Digest208) (position : Position) :
    Option Digest208 :=
  firstUnresolvedTarget parseC2Leaf truncateSha256 log treeDepth root
    position.val

theorem resolvePath_none_iff_firstUnresolvedTarget_isSome
    {Leaf : Type}
    (parseLeaf : RawHashInput → Option Leaf)
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) : ∀
    (height : Nat) (target : Digest208) (position : Nat),
    resolvePath parseLeaf truncateSha256 log height target position = none ↔
      (firstUnresolvedTarget parseLeaf truncateSha256 log height target
        position).isSome := by
  intro height
  induction height with
  | zero =>
      intro target position
      cases inputEquation : resolveInput truncateSha256 target log with
      | none => simp [resolvePath, firstUnresolvedTarget, inputEquation]
      | some input =>
          cases leafEquation : parseLeaf input with
          | none =>
              simp [resolvePath, firstUnresolvedTarget, inputEquation,
                leafEquation]
          | some leaf =>
              simp [resolvePath, firstUnresolvedTarget, inputEquation,
                leafEquation]
  | succ height inductionHypothesis =>
      intro target position
      cases inputEquation : resolveInput truncateSha256 target log with
      | none => simp [resolvePath, firstUnresolvedTarget, inputEquation]
      | some input =>
          cases typedEquation : parseTypedPreimage input with
          | none =>
              simp [resolvePath, firstUnresolvedTarget, inputEquation,
                typedEquation]
          | some typed =>
              cases typed with
              | c1Leaf value salt =>
                  simp [resolvePath, firstUnresolvedTarget, inputEquation,
                    typedEquation]
              | c2Leaf value salt =>
                  simp [resolvePath, firstUnresolvedTarget, inputEquation,
                    typedEquation]
              | node left right =>
                  by_cases direction : position.testBit height
                  · cases childEquation : resolvePath parseLeaf truncateSha256
                        log height right position with
                    | none =>
                        simpa [resolvePath, firstUnresolvedTarget,
                          inputEquation, typedEquation, direction,
                          childEquation] using
                            inductionHypothesis right position
                    | some child =>
                        simpa [resolvePath, firstUnresolvedTarget,
                          inputEquation, typedEquation, direction,
                          childEquation] using
                            inductionHypothesis right position
                  · have directionFalse : position.testBit height = false :=
                      Bool.eq_false_iff.mpr direction
                    cases childEquation : resolvePath parseLeaf truncateSha256
                        log height left position with
                    | none =>
                        simpa [resolvePath, firstUnresolvedTarget,
                          inputEquation, typedEquation, directionFalse,
                          childEquation] using
                            inductionHypothesis left position
                    | some child =>
                        simpa [resolvePath, firstUnresolvedTarget,
                          inputEquation, typedEquation, directionFalse,
                          childEquation] using
                            inductionHypothesis left position

theorem resolveC1Path_none_iff_firstUnresolvedC1Target_isSome
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (root : Digest208) (position : Position) :
    resolveC1Path truncateSha256 log root position = none ↔
      (firstUnresolvedC1Target truncateSha256 log root position).isSome := by
  exact resolvePath_none_iff_firstUnresolvedTarget_isSome parseC1Leaf
    truncateSha256 log treeDepth root position.val

theorem resolveC2Path_none_iff_firstUnresolvedC2Target_isSome
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (root : Digest208) (position : Position) :
    resolveC2Path truncateSha256 log root position = none ↔
      (firstUnresolvedC2Target truncateSha256 log root position).isSome := by
  exact resolvePath_none_iff_firstUnresolvedTarget_isSome parseC2Leaf
    truncateSha256 log treeDepth root position.val

def prefixResolutionTargetList
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog : OrderedRawQueryLog) (roots : Roots)
    (proof : TwoTreeOpeningProof) : List Digest208 :=
  (List.ofFn (fun ordinal : Fin disclosedQueryPairs =>
      firstUnresolvedC1Target truncateSha256 prefixLog roots.c1
        (proof ordinal).position)).filterMap id ++
    (List.ofFn (fun ordinal : Fin disclosedQueryPairs =>
      firstUnresolvedC2Target truncateSha256 prefixLog roots.c2
        (proof ordinal).position)).filterMap id

def prefixResolutionTargetSet
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog : OrderedRawQueryLog) (roots : Roots)
    (proof : TwoTreeOpeningProof) : Finset Digest208 :=
  (prefixResolutionTargetList truncateSha256 prefixLog roots proof).toFinset

private theorem filterMap_length_le {Alpha Beta : Type}
    (map : Alpha → Option Beta) : ∀ values : List Alpha,
    (values.filterMap map).length ≤ values.length := by
  intro values
  induction values with
  | nil => simp
  | cons value rest inductionHypothesis =>
      cases equation : map value with
      | none =>
          simp only [List.filterMap_cons, equation]
          exact inductionHypothesis.trans (Nat.le_succ _)
      | some mapped =>
          simp only [List.filterMap_cons, equation, List.length_cons]
          exact Nat.succ_le_succ inductionHypothesis

theorem prefixResolutionTargetList_length_le
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog : OrderedRawQueryLog) (roots : Roots)
    (proof : TwoTreeOpeningProof) :
    (prefixResolutionTargetList truncateSha256 prefixLog roots proof).length ≤
      2 * disclosedQueryPairs := by
  unfold prefixResolutionTargetList
  rw [List.length_append]
  have c1Bound := filterMap_length_le id
    (List.ofFn (fun ordinal : Fin disclosedQueryPairs =>
      firstUnresolvedC1Target truncateSha256 prefixLog roots.c1
        (proof ordinal).position))
  have c2Bound := filterMap_length_le id
    (List.ofFn (fun ordinal : Fin disclosedQueryPairs =>
      firstUnresolvedC2Target truncateSha256 prefixLog roots.c2
        (proof ordinal).position))
  simp only [List.length_ofFn] at c1Bound c2Bound
  omega

theorem prefixResolutionTargetSet_card_le
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog : OrderedRawQueryLog) (roots : Roots)
    (proof : TwoTreeOpeningProof) :
    (prefixResolutionTargetSet truncateSha256 prefixLog roots proof).card ≤
      2 * disclosedQueryPairs := by
  exact (List.toFinset_card_le _).trans
    (prefixResolutionTargetList_length_le truncateSha256 prefixLog roots proof)

theorem firstUnresolvedC1Target_mem_prefixResolutionTargetSet
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog : OrderedRawQueryLog) (roots : Roots)
    (proof : TwoTreeOpeningProof) (ordinal : Fin disclosedQueryPairs)
    (target : Digest208)
    (targetEquation : firstUnresolvedC1Target truncateSha256 prefixLog roots.c1
      (proof ordinal).position = some target) :
    target ∈ prefixResolutionTargetSet truncateSha256 prefixLog roots proof := by
  apply List.mem_toFinset.mpr
  apply List.mem_append_left
  apply List.mem_filterMap.mpr
  exact ⟨some target, List.mem_ofFn.mpr ⟨ordinal, targetEquation⟩, rfl⟩

theorem firstUnresolvedC2Target_mem_prefixResolutionTargetSet
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog : OrderedRawQueryLog) (roots : Roots)
    (proof : TwoTreeOpeningProof) (ordinal : Fin disclosedQueryPairs)
    (target : Digest208)
    (targetEquation : firstUnresolvedC2Target truncateSha256 prefixLog roots.c2
      (proof ordinal).position = some target) :
    target ∈ prefixResolutionTargetSet truncateSha256 prefixLog roots proof := by
  apply List.mem_toFinset.mpr
  apply List.mem_append_right
  apply List.mem_filterMap.mpr
  exact ⟨some target, List.mem_ofFn.mpr ⟨ordinal, targetEquation⟩, rfl⟩

/-! ## Every successful traversal is a prefix-covered opening -/

theorem resolvePath_success_authenticates_and_is_covered
    {Leaf : Type}
    (parseLeaf : RawHashInput → Option Leaf)
    (leafInput : Leaf → RawHashInput)
    (parseLeafExact : ∀ input leaf,
      parseLeaf input = some leaf → leafInput leaf = input)
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) : ∀
    (height : Nat) (target : Digest208) (position : Nat)
    (path : ResolvedPath Leaf height),
    resolvePath parseLeaf truncateSha256 log height target position =
        some path →
      foldPathAux truncateSha256 position
          (truncateSha256 (leafInput path.leaf))
          (List.ofFn path.siblings) = target ∧
        TraceIncludedInLog
          (leafInput path.leaf ::
            foldPathInputTrace truncateSha256 position
              (truncateSha256 (leafInput path.leaf))
              (List.ofFn path.siblings)) log := by
  intro height
  induction height with
  | zero =>
      intro target position path success
      cases inputEquation : resolveInput truncateSha256 target log with
      | none => simp [resolvePath, inputEquation] at success
      | some input =>
          cases leafEquation : parseLeaf input with
          | none => simp [resolvePath, inputEquation, leafEquation] at success
          | some leaf =>
              have pathExact : path = ⟨leaf, Fin.elim0⟩ := by
                simpa [resolvePath, inputEquation, leafEquation] using
                  success.symm
              subst path
              have leafInputExact := parseLeafExact input leaf leafEquation
              have inputDigest := resolveInput_success_digest truncateSha256
                target log input inputEquation
              have inputIn := resolveInput_success_mem truncateSha256
                target log input inputEquation
              constructor
              · simpa [foldPathAux, leafInputExact] using inputDigest
              · intro candidate candidateIn
                simp only [List.ofFn_zero, foldPathInputTrace,
                  List.mem_singleton] at candidateIn
                subst candidate
                simpa [leafInputExact] using inputIn
  | succ height inductionHypothesis =>
      intro target position path success
      cases inputEquation : resolveInput truncateSha256 target log with
      | none => simp [resolvePath, inputEquation] at success
      | some input =>
          cases typedEquation : parseTypedPreimage input with
          | none => simp [resolvePath, inputEquation, typedEquation] at success
          | some typed =>
              cases typed with
              | c1Leaf value salt =>
                  simp [resolvePath, inputEquation, typedEquation] at success
              | c2Leaf value salt =>
                  simp [resolvePath, inputEquation, typedEquation] at success
              | node left right =>
                  have inputDigest := resolveInput_success_digest
                    truncateSha256 target log input inputEquation
                  have inputIn := resolveInput_success_mem
                    truncateSha256 target log input inputEquation
                  have nodeInputExact :=
                    parseTypedPreimage_success_reserializes input
                      (.node left right) typedEquation
                  by_cases direction : position.testBit height
                  · cases childEquation : resolvePath parseLeaf truncateSha256
                        log height right position with
                    | none =>
                        simp [resolvePath, inputEquation, typedEquation,
                          direction, childEquation] at success
                    | some child =>
                        have pathExact : path = appendTopSibling child left := by
                          simpa [resolvePath, inputEquation, typedEquation,
                            direction, childEquation] using success.symm
                        subst path
                        have childCertificate := inductionHypothesis right
                          position child childEquation
                        have topDirection :
                            (position / 2 ^ height).testBit 0 = true := by
                          rw [Nat.testBit_div_two_pow]
                          simpa using direction
                        have siblingList :
                            List.ofFn (appendTopSibling child left).siblings =
                              List.ofFn child.siblings ++ [left] := by
                          simpa [appendTopSibling] using
                            (List.ofFn_fin_append child.siblings
                              (fun _ : Fin 1 => left))
                        constructor
                        · rw [siblingList]
                          change foldPathAux truncateSha256 position
                            (truncateSha256 (leafInput child.leaf))
                            (List.ofFn child.siblings ++ [left]) = target
                          rw [foldPathAux_append, childCertificate.1,
                            List.length_ofFn]
                          simpa [foldPathAux, topDirection, nodeInputExact]
                            using inputDigest
                        · rw [siblingList]
                          change TraceIncludedInLog
                            (leafInput child.leaf ::
                              foldPathInputTrace truncateSha256 position
                                (truncateSha256 (leafInput child.leaf))
                                (List.ofFn child.siblings ++ [left])) log
                          rw [foldPathInputTrace_append,
                            childCertificate.1, List.length_ofFn]
                          have traceExact :
                              foldPathInputTrace truncateSha256
                                  (position / 2 ^ height) right [left] =
                                [input] := by
                            simp [foldPathInputTrace, orderedNodeInput,
                              topDirection, nodeInputExact]
                          rw [traceExact]
                          change TraceIncludedInLog
                            ((leafInput child.leaf ::
                              foldPathInputTrace truncateSha256 position
                                (truncateSha256 (leafInput child.leaf))
                                (List.ofFn child.siblings)) ++ [input]) log
                          intro candidate candidateIn
                          rcases List.mem_append.mp candidateIn with
                            childInput | inputExact
                          · exact childCertificate.2 candidate childInput
                          · have : candidate = input := by
                              simpa using inputExact
                            subst candidate
                            exact inputIn
                  · have directionFalse : position.testBit height = false :=
                        Bool.eq_false_iff.mpr direction
                    cases childEquation : resolvePath parseLeaf truncateSha256
                        log height left position with
                    | none =>
                        simp [resolvePath, inputEquation, typedEquation,
                          directionFalse, childEquation] at success
                    | some child =>
                        have pathExact : path = appendTopSibling child right := by
                          simpa [resolvePath, inputEquation, typedEquation,
                            directionFalse, childEquation] using success.symm
                        subst path
                        have childCertificate := inductionHypothesis left
                          position child childEquation
                        have topDirection :
                            (position / 2 ^ height).testBit 0 = false := by
                          rw [Nat.testBit_div_two_pow]
                          simpa using directionFalse
                        have siblingList :
                            List.ofFn (appendTopSibling child right).siblings =
                              List.ofFn child.siblings ++ [right] := by
                          simpa [appendTopSibling] using
                            (List.ofFn_fin_append child.siblings
                              (fun _ : Fin 1 => right))
                        constructor
                        · rw [siblingList]
                          change foldPathAux truncateSha256 position
                            (truncateSha256 (leafInput child.leaf))
                            (List.ofFn child.siblings ++ [right]) = target
                          rw [foldPathAux_append, childCertificate.1,
                            List.length_ofFn]
                          simpa [foldPathAux, topDirection, nodeInputExact]
                            using inputDigest
                        · rw [siblingList]
                          change TraceIncludedInLog
                            (leafInput child.leaf ::
                              foldPathInputTrace truncateSha256 position
                                (truncateSha256 (leafInput child.leaf))
                                (List.ofFn child.siblings ++ [right])) log
                          rw [foldPathInputTrace_append,
                            childCertificate.1, List.length_ofFn]
                          have traceExact :
                              foldPathInputTrace truncateSha256
                                  (position / 2 ^ height) left [right] =
                                [input] := by
                            simp [foldPathInputTrace, orderedNodeInput,
                              topDirection, nodeInputExact]
                          rw [traceExact]
                          change TraceIncludedInLog
                            ((leafInput child.leaf ::
                              foldPathInputTrace truncateSha256 position
                                (truncateSha256 (leafInput child.leaf))
                                (List.ofFn child.siblings)) ++ [input]) log
                          intro candidate candidateIn
                          rcases List.mem_append.mp candidateIn with
                            childInput | inputExact
                          · exact childCertificate.2 candidate childInput
                          · have : candidate = input := by
                              simpa using inputExact
                            subst candidate
                            exact inputIn

/-! ## Prefix-fixed arbitrary completion -/

def prefixC1LeafAt (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (root : Digest208) (position : Position) : C1Leaf :=
  match resolveC1Path truncateSha256 log root position with
  | some path => path.leaf
  | none => defaultC1Leaf

def prefixC2LeafAt (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (root : Digest208) (position : Position) : C2Leaf :=
  match resolveC2Path truncateSha256 log root position with
  | some path => path.leaf
  | none => defaultC2Leaf

def extractPrefixFixedWords
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (roots : Roots) : ExtractedWords where
  c1 := List.ofFn (prefixC1LeafAt truncateSha256 log roots.c1)
  c2 := List.ofFn (prefixC2LeafAt truncateSha256 log roots.c2)

theorem getElem?_ofFn_at {Alpha : Type} {count : Nat}
    (values : Fin count → Alpha) (index : Fin count) :
    (List.ofFn values)[index.val]? = some (values index) := by
  rw [List.getElem?_eq_getElem (by simp)]
  simp

theorem resolvedC1Path_yields_covered_prefix_opening
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (root : Digest208) (position : Position)
    (path : ResolvedPath C1Leaf treeDepth)
    (resolved : resolveC1Path truncateSha256 log root position = some path) :
    C1CoveredCanonicalOpening truncateSha256
      (extractPrefixFixedWords truncateSha256 log ⟨root, root⟩).c1
      root position log := by
  have genericResolved :
      resolvePath parseC1Leaf truncateSha256 log treeDepth root position.val =
        some path := by
    simpa [resolveC1Path] using resolved
  have certificate := resolvePath_success_authenticates_and_is_covered
    parseC1Leaf (fun leaf => serialize (.c1Leaf leaf.value leaf.salt))
    parseC1Leaf_success_reserializes truncateSha256 log treeDepth root
    position.val path genericResolved
  refine ⟨path.leaf, path.siblings, ?_, ?_, ?_⟩
  · have atPosition := getElem?_ofFn_at
      (prefixC1LeafAt truncateSha256 log root) position
    simpa only [extractPrefixFixedWords, prefixC1LeafAt, resolved,
      Option.some.injEq] using atPosition
  · simpa [foldPath, c1LeafDigest] using certificate.1
  · simpa [openingInputTrace, openingRawInputTrace] using certificate.2

theorem resolvedC2Path_yields_covered_prefix_opening
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (root : Digest208) (position : Position)
    (path : ResolvedPath C2Leaf treeDepth)
    (resolved : resolveC2Path truncateSha256 log root position = some path) :
    C2CoveredCanonicalOpening truncateSha256
      (extractPrefixFixedWords truncateSha256 log ⟨root, root⟩).c2
      root position log := by
  have genericResolved :
      resolvePath parseC2Leaf truncateSha256 log treeDepth root position.val =
        some path := by
    simpa [resolveC2Path] using resolved
  have certificate := resolvePath_success_authenticates_and_is_covered
    parseC2Leaf (fun leaf => serialize (.c2Leaf leaf.value leaf.salt))
    parseC2Leaf_success_reserializes truncateSha256 log treeDepth root
    position.val path genericResolved
  refine ⟨path.leaf, path.siblings, ?_, ?_, ?_⟩
  · have atPosition := getElem?_ofFn_at
      (prefixC2LeafAt truncateSha256 log root) position
    simpa only [extractPrefixFixedWords, prefixC2LeafAt, resolved,
      Option.some.injEq] using atPosition
  · simpa [foldPath, c2LeafDigest] using certificate.1
  · simpa [openingInputTrace, openingRawInputTrace] using certificate.2

def PrefixPathResolutionFailure
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog : OrderedRawQueryLog) (roots : Roots)
    (proof : TwoTreeOpeningProof) : Prop :=
  ∃ ordinal : Fin disclosedQueryPairs,
    resolveC1Path truncateSha256 prefixLog roots.c1
        (proof ordinal).position = none ∨
      resolveC2Path truncateSha256 prefixLog roots.c2
        (proof ordinal).position = none

theorem prefixPathResolutionFailure_yields_firstTarget
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog : OrderedRawQueryLog) (roots : Roots)
    (proof : TwoTreeOpeningProof)
    (failure : PrefixPathResolutionFailure truncateSha256 prefixLog roots
      proof) :
    ∃ target ∈ prefixResolutionTargetSet truncateSha256 prefixLog roots proof,
      (∃ ordinal : Fin disclosedQueryPairs,
        firstUnresolvedC1Target truncateSha256 prefixLog roots.c1
          (proof ordinal).position = some target) ∨
      (∃ ordinal : Fin disclosedQueryPairs,
        firstUnresolvedC2Target truncateSha256 prefixLog roots.c2
          (proof ordinal).position = some target) := by
  obtain ⟨ordinal, c1Failure | c2Failure⟩ := failure
  · have targetExists :=
      (resolveC1Path_none_iff_firstUnresolvedC1Target_isSome
        truncateSha256 prefixLog roots.c1 (proof ordinal).position).mp
          c1Failure
    cases targetEquation : firstUnresolvedC1Target truncateSha256 prefixLog
        roots.c1 (proof ordinal).position with
    | none => simp [targetEquation] at targetExists
    | some target =>
        exact ⟨target,
          firstUnresolvedC1Target_mem_prefixResolutionTargetSet truncateSha256
            prefixLog roots proof ordinal target targetEquation,
          Or.inl ⟨ordinal, targetEquation⟩⟩
  · have targetExists :=
      (resolveC2Path_none_iff_firstUnresolvedC2Target_isSome
        truncateSha256 prefixLog roots.c2 (proof ordinal).position).mp
          c2Failure
    cases targetEquation : firstUnresolvedC2Target truncateSha256 prefixLog
        roots.c2 (proof ordinal).position with
    | none => simp [targetEquation] at targetExists
    | some target =>
        exact ⟨target,
          firstUnresolvedC2Target_mem_prefixResolutionTargetSet truncateSha256
            prefixLog roots proof ordinal target targetEquation,
          Or.inr ⟨ordinal, targetEquation⟩⟩

theorem no_prefix_path_resolution_failure_yields_paths
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog : OrderedRawQueryLog) (roots : Roots)
    (proof : TwoTreeOpeningProof)
    (noFailure : ¬ PrefixPathResolutionFailure truncateSha256 prefixLog
      roots proof) :
    (∀ ordinal : Fin disclosedQueryPairs,
      ∃ path : ResolvedPath C1Leaf treeDepth,
        resolveC1Path truncateSha256 prefixLog roots.c1
          (proof ordinal).position = some path) ∧
    (∀ ordinal : Fin disclosedQueryPairs,
      ∃ path : ResolvedPath C2Leaf treeDepth,
        resolveC2Path truncateSha256 prefixLog roots.c2
          (proof ordinal).position = some path) := by
  constructor
  · intro ordinal
    cases equation : resolveC1Path truncateSha256 prefixLog roots.c1
        (proof ordinal).position with
    | none => exact False.elim (noFailure ⟨ordinal, Or.inl equation⟩)
    | some path => exact ⟨path, rfl⟩
  · intro ordinal
    cases equation : resolveC2Path truncateSha256 prefixLog roots.c2
        (proof ordinal).position with
    | none => exact False.elim (noFailure ⟨ordinal, Or.inr equation⟩)
    | some path => exact ⟨path, rfl⟩

theorem trace_inclusion_trans
    (left middle right : OrderedRawQueryLog)
    (leftInMiddle : TraceIncludedInLog left middle)
    (middleInRight : TraceIncludedInLog middle right) :
    TraceIncludedInLog left right := by
  intro input inputIn
  exact middleInRight input (leftInMiddle input inputIn)

/-- The deterministic K1.2 conclusion for an oracle fixed at the prover-final
prefix.  No complete-tree/recommitment premise occurs: unopened subtrees are
arbitrarily completed. -/
theorem accepted_openings_are_prefix_fixed_projections
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog fullLog : OrderedRawQueryLog)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (accepted : accepted_two_tree_openings truncateSha256 roots proof)
    (prefixIncluded : TraceIncludedInLog prefixLog fullLog)
    (noResolutionFailure :
      ¬ PrefixPathResolutionFailure truncateSha256 prefixLog roots proof)
    (c1SuppliedCovered : ∀ ordinal : Fin disclosedQueryPairs,
      TraceIncludedInLog
        (openingInputTrace truncateSha256 (proof ordinal).position
          (.c1Leaf (proof ordinal).c1Value (proof ordinal).sharedSalt)
          (proof ordinal).c1Siblings) fullLog)
    (c2SuppliedCovered : ∀ ordinal : Fin disclosedQueryPairs,
      TraceIncludedInLog
        (openingInputTrace truncateSha256 (proof ordinal).position
          (.c2Leaf (proof ordinal).c2Value (proof ordinal).sharedSalt)
          (proof ordinal).c2Siblings) fullLog)
    (noCollision :
      ¬ RawLogTruncatedDigestCollision truncateSha256 fullLog) :
    disclosuresAreProjections
      (extractPrefixFixedWords truncateSha256 prefixLog roots) proof := by
  have resolvedPaths := no_prefix_path_resolution_failure_yields_paths
    truncateSha256 prefixLog roots proof noResolutionFailure
  apply accepted_openings_are_projections_of_covered_paths
    truncateSha256 (extractPrefixFixedWords truncateSha256 prefixLog roots)
      roots proof fullLog accepted
  · intro ordinal
    obtain ⟨path, resolved⟩ := resolvedPaths.1 ordinal
    have covered := resolvedC1Path_yields_covered_prefix_opening
      truncateSha256 prefixLog roots.c1 (proof ordinal).position path resolved
    obtain ⟨leaf, siblings, leafAt, authenticates, traceCovered⟩ := covered
    exact ⟨leaf, siblings, leafAt, authenticates,
      trace_inclusion_trans _ _ _ traceCovered prefixIncluded⟩
  · intro ordinal
    obtain ⟨path, resolved⟩ := resolvedPaths.2 ordinal
    have covered := resolvedC2Path_yields_covered_prefix_opening
      truncateSha256 prefixLog roots.c2 (proof ordinal).position path resolved
    obtain ⟨leaf, siblings, leafAt, authenticates, traceCovered⟩ := covered
    exact ⟨leaf, siblings, leafAt, authenticates,
      trace_inclusion_trans _ _ _ traceCovered prefixIncluded⟩
  · exact c1SuppliedCovered
  · exact c2SuppliedCovered
  · exact noCollision

@[simp] theorem extractPrefixFixedWords_c1_length
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (roots : Roots) :
    (extractPrefixFixedWords truncateSha256 log roots).c1.length =
      2 ^ treeDepth := by
  simp [extractPrefixFixedWords]

@[simp] theorem extractPrefixFixedWords_c2_length
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) (roots : Roots) :
    (extractPrefixFixedWords truncateSha256 log roots).c2.length =
      2 ^ treeDepth := by
  simp [extractPrefixFixedWords]

#print axioms parseTypedPreimage_success_reserializes
#print axioms resolveInput_success_digest
#print axioms resolveInput_success_mem
#print axioms resolvePath_none_iff_firstUnresolvedTarget_isSome
#print axioms prefixResolutionTargetList_length_le
#print axioms prefixResolutionTargetSet_card_le
#print axioms prefixPathResolutionFailure_yields_firstTarget
#print axioms resolvePath_success_authenticates_and_is_covered
#print axioms resolvedC1Path_yields_covered_prefix_opening
#print axioms resolvedC2Path_yields_covered_prefix_opening
#print axioms accepted_openings_are_prefix_fixed_projections
#print axioms extractPrefixFixedWords_c1_length
#print axioms extractPrefixFixedWords_c2_length

end AspisPool.V7MerklePartialPathExtractor
