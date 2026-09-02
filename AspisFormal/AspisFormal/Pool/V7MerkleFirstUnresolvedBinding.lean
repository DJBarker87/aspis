import AspisFormal.Pool.V7MerklePartialPathExtractor
import AspisFormal.Pool.V7MerkleParserRoundtrip

/-!
# Binding a first unresolved Merkle target to a later oracle hit

This is the deterministic middle of the prefix-fixed K1.2 reduction.  A
root-to-leaf authenticating path is represented in the same direction as the
prefix resolver.  If the resolver stops at a digest, then either the concrete
authenticating preimage for that digest was not in the prover-final prefix, or
a distinct raw input in the shared log has the same 208-bit answer.

The theorem is deliberately independent of probability.  The later lazy-RO
game maps the first alternative to the at-most-32 causal target set and the
second to the one shared birthday event.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisPool.V7MerkleFirstUnresolvedBinding

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisPool.V7MerklePartialPathExtractor
open AspisPool.V7MerkleParserRoundtrip

/-! ## Exact root-to-leaf authentication witness -/

inductive AuthenticatingPath {Leaf : Type}
    (parseLeaf : RawHashInput → Option Leaf)
    (truncateSha256 : RawHashInput → Digest208) :
    (height : Nat) → Digest208 → Nat → Type
  | leaf (target : Digest208) (position : Nat)
      (input : RawHashInput) (value : Leaf)
      (digestExact : truncateSha256 input = target)
      (parseExact : parseLeaf input = some value) :
      AuthenticatingPath parseLeaf truncateSha256 0 target position
  | nodeTrue {height : Nat} (target : Digest208) (position : Nat)
      (input : RawHashInput) (left right : Digest208)
      (digestExact : truncateSha256 input = target)
      (parseExact : parseTypedPreimage input = some (.node left right))
      (direction : position.testBit height = true)
      (child : AuthenticatingPath parseLeaf truncateSha256 height right
        position) :
      AuthenticatingPath parseLeaf truncateSha256 (height + 1) target position
  | nodeFalse {height : Nat} (target : Digest208) (position : Nat)
      (input : RawHashInput) (left right : Digest208)
      (digestExact : truncateSha256 input = target)
      (parseExact : parseTypedPreimage input = some (.node left right))
      (direction : position.testBit height = false)
      (child : AuthenticatingPath parseLeaf truncateSha256 height left
        position) :
      AuthenticatingPath parseLeaf truncateSha256 (height + 1) target position

def AuthenticatingPath.inputs {Leaf : Type}
    {parseLeaf : RawHashInput → Option Leaf}
    {truncateSha256 : RawHashInput → Digest208} :
    {height : Nat} → {target : Digest208} → {position : Nat} →
      AuthenticatingPath parseLeaf truncateSha256 height target position →
        List RawHashInput
  | _, _, _, .leaf _ _ input _ _ _ => [input]
  | _, _, _, .nodeTrue _ _ input _ _ _ _ _ child =>
      input :: child.inputs
  | _, _, _, .nodeFalse _ _ input _ _ _ _ _ child =>
      input :: child.inputs

/-- A conventional bottom-up opening trace has an equivalent root-to-leaf
authentication witness.  Its input list is exactly the reverse of the
deployed leaf-then-node call order. -/
theorem authenticatingPath_of_bottomUpOpening
    {Leaf : Type}
    (parseLeaf : RawHashInput → Option Leaf)
    (truncateSha256 : RawHashInput → Digest208)
    (position : Nat) (leafInput : RawHashInput) (leaf : Leaf)
    (leafParsed : parseLeaf leafInput = some leaf) :
    ∀ siblings : List Digest208,
    ∃ path : AuthenticatingPath parseLeaf truncateSha256 siblings.length
        (foldPathAux truncateSha256 position
          (truncateSha256 leafInput) siblings) position,
      path.inputs =
        (leafInput :: foldPathInputTrace truncateSha256 position
          (truncateSha256 leafInput) siblings).reverse := by
  intro siblings
  induction siblings using List.reverseRecOn with
  | nil =>
      exact ⟨.leaf (truncateSha256 leafInput) position leafInput leaf rfl
        leafParsed, by simp [AuthenticatingPath.inputs,
          foldPathInputTrace]⟩
  | append_singleton rest top inductionHypothesis =>
      obtain ⟨child, childInputs⟩ := inductionHypothesis
      let childRoot := foldPathAux truncateSha256 position
        (truncateSha256 leafInput) rest
      let parentPosition := position / 2 ^ rest.length
      let nodeInput := orderedNodeInput parentPosition childRoot top
      have topDirection :
          parentPosition.testBit 0 = position.testBit rest.length := by
        simp only [parentPosition, Nat.testBit_div_two_pow, Nat.zero_add]
      have rootExact :
          foldPathAux truncateSha256 position (truncateSha256 leafInput)
              (rest ++ [top]) = truncateSha256 nodeInput := by
        rw [AspisPool.V7MerkleCanonicalOpening.foldPathAux_append]
        change foldPathAux truncateSha256 parentPosition childRoot [top] =
          truncateSha256 nodeInput
        rw [foldPathAux_cons]
        rfl
      have traceExact :
          foldPathInputTrace truncateSha256 position
              (truncateSha256 leafInput) (rest ++ [top]) =
            foldPathInputTrace truncateSha256 position
                (truncateSha256 leafInput) rest ++ [nodeInput] := by
        rw [foldPathInputTrace_append]
        change foldPathInputTrace truncateSha256 position
            (truncateSha256 leafInput) rest ++
              foldPathInputTrace truncateSha256 parentPosition childRoot [top] =
          foldPathInputTrace truncateSha256 position
            (truncateSha256 leafInput) rest ++ [nodeInput]
        simp [foldPathInputTrace, nodeInput]
      by_cases direction : position.testBit rest.length
      · have parentDirection : parentPosition.testBit 0 = true := by
          rw [topDirection]
          exact direction
        have inputExact :
            nodeInput = serialize (.node top childRoot) := by
          simp [nodeInput, orderedNodeInput, parentDirection]
        have parsedExact :
            parseTypedPreimage nodeInput = some (.node top childRoot) := by
          rw [inputExact]
          exact parse_serialize_typed_preimage _
        rw [List.length_append, List.length_singleton]
        rw [rootExact]
        refine ⟨.nodeTrue (truncateSha256 nodeInput) position nodeInput top
          childRoot rfl parsedExact direction child, ?_⟩
        simp only [AuthenticatingPath.inputs]
        rw [traceExact, List.reverse_cons, List.reverse_append,
          List.reverse_singleton, List.singleton_append, childInputs]
        simp only [List.reverse_cons]
        rfl
      · have directionFalse : position.testBit rest.length = false :=
          Bool.eq_false_iff.mpr direction
        have parentDirection : parentPosition.testBit 0 = false := by
          rw [topDirection]
          exact directionFalse
        have inputExact :
            nodeInput = serialize (.node childRoot top) := by
          simp [nodeInput, orderedNodeInput, parentDirection]
        have parsedExact :
            parseTypedPreimage nodeInput = some (.node childRoot top) := by
          rw [inputExact]
          exact parse_serialize_typed_preimage _
        rw [List.length_append, List.length_singleton]
        rw [rootExact]
        refine ⟨.nodeFalse (truncateSha256 nodeInput) position nodeInput
          childRoot top rfl parsedExact directionFalse child, ?_⟩
        simp only [AuthenticatingPath.inputs]
        rw [traceExact, List.reverse_cons, List.reverse_append,
          List.reverse_singleton, List.singleton_append, childInputs]
        simp only [List.reverse_cons]
        rfl

theorem acceptedC1Opening_yields_authenticatingPath
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (accepted : accepted_two_tree_openings truncateSha256 roots proof)
    (ordinal : Fin disclosedQueryPairs) :
    ∃ path : AuthenticatingPath parseC1Leaf truncateSha256
        (List.ofFn (proof ordinal).c1Siblings).length
        (foldPathAux truncateSha256 (proof ordinal).position.val
          (c1DisclosedLeafDigest truncateSha256 (proof ordinal))
          (List.ofFn (proof ordinal).c1Siblings))
        (proof ordinal).position.val,
      path.inputs =
        (openingInputTrace truncateSha256 (proof ordinal).position
          (.c1Leaf (proof ordinal).c1Value (proof ordinal).sharedSalt)
          (proof ordinal).c1Siblings).reverse ∧
      foldPathAux truncateSha256 (proof ordinal).position.val
          (c1DisclosedLeafDigest truncateSha256 (proof ordinal))
          (List.ofFn (proof ordinal).c1Siblings) = roots.c1 := by
  let leaf : C1Leaf :=
    ⟨(proof ordinal).c1Value, (proof ordinal).sharedSalt⟩
  let leafInput := serialize (.c1Leaf leaf.value leaf.salt)
  have leafParsed : parseC1Leaf leafInput = some leaf := by
    simp [parseC1Leaf, leafInput, leaf, parse_serialize_typed_preimage]
  obtain ⟨path, pathInputs⟩ := authenticatingPath_of_bottomUpOpening
    parseC1Leaf truncateSha256 (proof ordinal).position.val leafInput leaf
      leafParsed (List.ofFn (proof ordinal).c1Siblings)
  have rootExact := (accepted.2 ordinal).1
  change foldPathAux truncateSha256 (proof ordinal).position.val
      (truncateSha256 leafInput) (List.ofFn (proof ordinal).c1Siblings) =
    roots.c1 at rootExact
  change ∃ candidate : AuthenticatingPath parseC1Leaf truncateSha256
      (List.ofFn (proof ordinal).c1Siblings).length
      (foldPathAux truncateSha256 (proof ordinal).position.val
        (truncateSha256 leafInput) (List.ofFn (proof ordinal).c1Siblings))
      (proof ordinal).position.val,
    candidate.inputs =
        (leafInput :: foldPathInputTrace truncateSha256
          (proof ordinal).position.val (truncateSha256 leafInput)
          (List.ofFn (proof ordinal).c1Siblings)).reverse ∧
      foldPathAux truncateSha256 (proof ordinal).position.val
        (truncateSha256 leafInput) (List.ofFn (proof ordinal).c1Siblings) =
          roots.c1
  exact ⟨path, pathInputs, rootExact⟩

theorem acceptedC2Opening_yields_authenticatingPath
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (accepted : accepted_two_tree_openings truncateSha256 roots proof)
    (ordinal : Fin disclosedQueryPairs) :
    ∃ path : AuthenticatingPath parseC2Leaf truncateSha256
        (List.ofFn (proof ordinal).c2Siblings).length
        (foldPathAux truncateSha256 (proof ordinal).position.val
          (c2DisclosedLeafDigest truncateSha256 (proof ordinal))
          (List.ofFn (proof ordinal).c2Siblings))
        (proof ordinal).position.val,
      path.inputs =
        (openingInputTrace truncateSha256 (proof ordinal).position
          (.c2Leaf (proof ordinal).c2Value (proof ordinal).sharedSalt)
          (proof ordinal).c2Siblings).reverse ∧
      foldPathAux truncateSha256 (proof ordinal).position.val
          (c2DisclosedLeafDigest truncateSha256 (proof ordinal))
          (List.ofFn (proof ordinal).c2Siblings) = roots.c2 := by
  let leaf : C2Leaf :=
    ⟨(proof ordinal).c2Value, (proof ordinal).sharedSalt⟩
  let leafInput := serialize (.c2Leaf leaf.value leaf.salt)
  have leafParsed : parseC2Leaf leafInput = some leaf := by
    simp [parseC2Leaf, leafInput, leaf, parse_serialize_typed_preimage]
  obtain ⟨path, pathInputs⟩ := authenticatingPath_of_bottomUpOpening
    parseC2Leaf truncateSha256 (proof ordinal).position.val leafInput leaf
      leafParsed (List.ofFn (proof ordinal).c2Siblings)
  have rootExact := (accepted.2 ordinal).2
  change foldPathAux truncateSha256 (proof ordinal).position.val
      (truncateSha256 leafInput) (List.ofFn (proof ordinal).c2Siblings) =
    roots.c2 at rootExact
  change ∃ candidate : AuthenticatingPath parseC2Leaf truncateSha256
      (List.ofFn (proof ordinal).c2Siblings).length
      (foldPathAux truncateSha256 (proof ordinal).position.val
        (truncateSha256 leafInput) (List.ofFn (proof ordinal).c2Siblings))
      (proof ordinal).position.val,
    candidate.inputs =
        (leafInput :: foldPathInputTrace truncateSha256
          (proof ordinal).position.val (truncateSha256 leafInput)
          (List.ofFn (proof ordinal).c2Siblings)).reverse ∧
      foldPathAux truncateSha256 (proof ordinal).position.val
        (truncateSha256 leafInput) (List.ofFn (proof ordinal).c2Siblings) =
          roots.c2
  exact ⟨path, pathInputs, rootExact⟩

theorem resolveInput_none_excludes_matching_member
    (truncateSha256 : RawHashInput → Digest208)
    (target : Digest208) (log : OrderedRawQueryLog)
    (notResolved : resolveInput truncateSha256 target log = none)
    (input : RawHashInput) (inputIn : input ∈ log) :
    truncateSha256 input ≠ target := by
  unfold resolveInput at notResolved
  have predicateFalse := List.find?_eq_none.mp notResolved input inputIn
  exact fun digestExact => by
    have predicateTrue : decide (truncateSha256 input = target) = true :=
      decide_eq_true digestExact
    rw [predicateTrue] at predicateFalse
    contradiction

def LaterTargetHit {Leaf : Type}
    {parseLeaf : RawHashInput → Option Leaf}
    {truncateSha256 : RawHashInput → Digest208}
    {height : Nat} {root : Digest208} {position : Nat}
    (path : AuthenticatingPath parseLeaf truncateSha256 height root position)
    (prefixLog : OrderedRawQueryLog) (target : Digest208) : Prop :=
  ∃ input ∈ path.inputs,
    input ∉ prefixLog ∧ truncateSha256 input = target

/-! ## First-unresolved binding theorem -/

theorem firstUnresolvedTarget_yields_later_hit_or_collision
    {Leaf : Type}
    (parseLeaf : RawHashInput → Option Leaf)
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog fullLog : OrderedRawQueryLog)
    (prefixIncluded : TraceIncludedInLog prefixLog fullLog) : ∀
    {height : Nat} {root : Digest208} {position : Nat}
    (path : AuthenticatingPath parseLeaf truncateSha256 height root position)
    (pathIncluded : TraceIncludedInLog path.inputs fullLog)
    (target : Digest208)
    (firstTarget : firstUnresolvedTarget parseLeaf truncateSha256 prefixLog
      height root position = some target),
    LaterTargetHit path prefixLog target ∨
      RawLogTruncatedDigestCollision truncateSha256 fullLog := by
  intro height root position path
  induction path with
  | leaf root position input value digestExact parseExact =>
      intro pathIncluded target firstTarget
      cases resolution : resolveInput truncateSha256 root prefixLog with
      | none =>
          have targetExact : target = root := by
            simpa [firstUnresolvedTarget, resolution] using firstTarget.symm
          apply Or.inl
          refine ⟨input, by simp [AuthenticatingPath.inputs], ?_, ?_⟩
          · intro inputIn
            exact (resolveInput_none_excludes_matching_member truncateSha256
              root prefixLog resolution input inputIn) digestExact
          · simpa [targetExact] using digestExact
      | some resolved =>
          have resolvedDigest := resolveInput_success_digest truncateSha256
            root prefixLog resolved resolution
          have resolvedInPrefix := resolveInput_success_mem truncateSha256
            root prefixLog resolved resolution
          cases resolvedLeaf : parseLeaf resolved with
          | none =>
              have targetExact : target = root := by
                simpa [firstUnresolvedTarget, resolution, resolvedLeaf] using
                  firstTarget.symm
              by_cases sameInput : resolved = input
              · subst resolved
                rw [parseExact] at resolvedLeaf
                contradiction
              · exact Or.inr ⟨resolved,
                  prefixIncluded resolved resolvedInPrefix,
                  input, pathIncluded input (by simp [AuthenticatingPath.inputs]),
                  sameInput,
                  resolvedDigest.trans digestExact.symm⟩
          | some resolvedValue =>
              simp [firstUnresolvedTarget, resolution, resolvedLeaf] at firstTarget
  | @nodeTrue height root position input left right digestExact parseExact
      direction child inductionHypothesis =>
      intro pathIncluded target firstTarget
      cases resolution : resolveInput truncateSha256 root prefixLog with
      | none =>
          have targetExact : target = root := by
            simpa [firstUnresolvedTarget, resolution] using firstTarget.symm
          apply Or.inl
          refine ⟨input, by simp [AuthenticatingPath.inputs], ?_, ?_⟩
          · intro inputIn
            exact (resolveInput_none_excludes_matching_member truncateSha256
              root prefixLog resolution input inputIn) digestExact
          · simpa [targetExact] using digestExact
      | some resolved =>
          have resolvedDigest := resolveInput_success_digest truncateSha256
            root prefixLog resolved resolution
          have resolvedInPrefix := resolveInput_success_mem truncateSha256
            root prefixLog resolved resolution
          by_cases sameInput : resolved = input
          · subst resolved
            have childFirst : firstUnresolvedTarget parseLeaf truncateSha256
                prefixLog height right position = some target := by
              simpa [firstUnresolvedTarget, resolution, parseExact, direction]
                using firstTarget
            have childIncluded : TraceIncludedInLog child.inputs fullLog := by
              intro candidate candidateIn
              exact pathIncluded candidate (by
                simp only [AuthenticatingPath.inputs, List.mem_cons]
                exact Or.inr candidateIn)
            obtain later | collision := inductionHypothesis childIncluded target
              childFirst
            · exact Or.inl (by
                obtain ⟨lateInput, lateIn, lateNotPrefix, lateDigest⟩ := later
                exact ⟨lateInput, by
                    simp only [AuthenticatingPath.inputs, List.mem_cons]
                    exact Or.inr lateIn,
                  lateNotPrefix, lateDigest⟩)
            · exact Or.inr collision
          · exact Or.inr ⟨resolved,
              prefixIncluded resolved resolvedInPrefix,
              input, pathIncluded input (by simp [AuthenticatingPath.inputs]),
              sameInput, resolvedDigest.trans digestExact.symm⟩
  | @nodeFalse height root position input left right digestExact parseExact
      direction child inductionHypothesis =>
      intro pathIncluded target firstTarget
      cases resolution : resolveInput truncateSha256 root prefixLog with
      | none =>
          have targetExact : target = root := by
            simpa [firstUnresolvedTarget, resolution] using firstTarget.symm
          apply Or.inl
          refine ⟨input, by simp [AuthenticatingPath.inputs], ?_, ?_⟩
          · intro inputIn
            exact (resolveInput_none_excludes_matching_member truncateSha256
              root prefixLog resolution input inputIn) digestExact
          · simpa [targetExact] using digestExact
      | some resolved =>
          have resolvedDigest := resolveInput_success_digest truncateSha256
            root prefixLog resolved resolution
          have resolvedInPrefix := resolveInput_success_mem truncateSha256
            root prefixLog resolved resolution
          by_cases sameInput : resolved = input
          · subst resolved
            have childFirst : firstUnresolvedTarget parseLeaf truncateSha256
                prefixLog height left position = some target := by
              simpa [firstUnresolvedTarget, resolution, parseExact, direction]
                using firstTarget
            have childIncluded : TraceIncludedInLog child.inputs fullLog := by
              intro candidate candidateIn
              exact pathIncluded candidate (by
                simp only [AuthenticatingPath.inputs, List.mem_cons]
                exact Or.inr candidateIn)
            obtain later | collision := inductionHypothesis childIncluded target
              childFirst
            · exact Or.inl (by
                obtain ⟨lateInput, lateIn, lateNotPrefix, lateDigest⟩ := later
                exact ⟨lateInput, by
                    simp only [AuthenticatingPath.inputs, List.mem_cons]
                    exact Or.inr lateIn,
                  lateNotPrefix, lateDigest⟩)
            · exact Or.inr collision
          · exact Or.inr ⟨resolved,
              prefixIncluded resolved resolvedInPrefix,
              input, pathIncluded input (by simp [AuthenticatingPath.inputs]),
              sameInput, resolvedDigest.trans digestExact.symm⟩

/-! ## Two-tree accepted-opening closure -/

def PrefixResolutionLateTargetHit
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog fullLog : OrderedRawQueryLog) (roots : Roots)
    (proof : TwoTreeOpeningProof) : Prop :=
  ∃ target ∈ prefixResolutionTargetSet truncateSha256 prefixLog roots proof,
    ∃ input ∈ fullLog,
      input ∉ prefixLog ∧ truncateSha256 input = target

/-- An accepted sampled path that is unresolved in the prover-final prefix is
not an unclassified extraction failure.  It produces either a later shared-RO
input hitting one of the at-most-32 causal targets or a raw 208-bit collision
in the one combined C1/C2/verifier log. -/
theorem accepted_prefixResolutionFailure_yields_late_hit_or_collision
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog fullLog : OrderedRawQueryLog) (roots : Roots)
    (proof : TwoTreeOpeningProof)
    (accepted : accepted_two_tree_openings truncateSha256 roots proof)
    (prefixIncluded : TraceIncludedInLog prefixLog fullLog)
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
    (failure : PrefixPathResolutionFailure truncateSha256 prefixLog roots
      proof) :
    PrefixResolutionLateTargetHit truncateSha256 prefixLog fullLog roots proof ∨
      RawLogTruncatedDigestCollision truncateSha256 fullLog := by
  obtain ⟨target, targetIn,
      (⟨ordinal, targetEquation⟩ | ⟨ordinal, targetEquation⟩)⟩ :=
    prefixPathResolutionFailure_yields_firstTarget truncateSha256 prefixLog
      roots proof failure
  · obtain ⟨path, pathInputs, rootExact⟩ :=
      acceptedC1Opening_yields_authenticatingPath truncateSha256 roots proof
        accepted ordinal
    have pathIncluded : TraceIncludedInLog path.inputs fullLog := by
      intro input inputIn
      apply c1SuppliedCovered ordinal input
      rw [pathInputs] at inputIn
      exact List.mem_reverse.mp inputIn
    have computedFirst :
        firstUnresolvedTarget parseC1Leaf truncateSha256 prefixLog
            (List.ofFn (proof ordinal).c1Siblings).length
            (foldPathAux truncateSha256 (proof ordinal).position.val
              (c1DisclosedLeafDigest truncateSha256 (proof ordinal))
              (List.ofFn (proof ordinal).c1Siblings))
            (proof ordinal).position.val = some target := by
      rw [List.length_ofFn, rootExact]
      simpa [firstUnresolvedC1Target] using targetEquation
    obtain later | collision :=
      firstUnresolvedTarget_yields_later_hit_or_collision parseC1Leaf
        truncateSha256 prefixLog fullLog prefixIncluded path pathIncluded target
          computedFirst
    · apply Or.inl
      obtain ⟨input, inputInPath, inputNotPrefix, inputDigest⟩ := later
      exact ⟨target, targetIn, input, pathIncluded input inputInPath,
        inputNotPrefix, inputDigest⟩
    · exact Or.inr collision
  · obtain ⟨path, pathInputs, rootExact⟩ :=
      acceptedC2Opening_yields_authenticatingPath truncateSha256 roots proof
        accepted ordinal
    have pathIncluded : TraceIncludedInLog path.inputs fullLog := by
      intro input inputIn
      apply c2SuppliedCovered ordinal input
      rw [pathInputs] at inputIn
      exact List.mem_reverse.mp inputIn
    have computedFirst :
        firstUnresolvedTarget parseC2Leaf truncateSha256 prefixLog
            (List.ofFn (proof ordinal).c2Siblings).length
            (foldPathAux truncateSha256 (proof ordinal).position.val
              (c2DisclosedLeafDigest truncateSha256 (proof ordinal))
              (List.ofFn (proof ordinal).c2Siblings))
            (proof ordinal).position.val = some target := by
      rw [List.length_ofFn, rootExact]
      simpa [firstUnresolvedC2Target] using targetEquation
    obtain later | collision :=
      firstUnresolvedTarget_yields_later_hit_or_collision parseC2Leaf
        truncateSha256 prefixLog fullLog prefixIncluded path pathIncluded target
          computedFirst
    · apply Or.inl
      obtain ⟨input, inputInPath, inputNotPrefix, inputDigest⟩ := later
      exact ⟨target, targetIn, input, pathIncluded input inputInPath,
        inputNotPrefix, inputDigest⟩
    · exact Or.inr collision

/-- An accepted two-tree opening is already a projection of the word fixed by
the chosen chronological prefix, unless the remaining shared-oracle execution
hits a first-unresolved 208-bit target or contains a truncated-digest
collision.  This prefix-agnostic gate also applies when the Fiat--Shamir q16
coordinate was exposed before prover return. -/
theorem accepted_openings_yield_prefix_projections_or_late_hit_or_collision
    (truncateSha256 : RawHashInput → Digest208)
    (prefixLog fullLog : OrderedRawQueryLog) (roots : Roots)
    (proof : TwoTreeOpeningProof)
    (accepted : accepted_two_tree_openings truncateSha256 roots proof)
    (prefixIncluded : TraceIncludedInLog prefixLog fullLog)
    (c1SuppliedCovered : ∀ ordinal : Fin disclosedQueryPairs,
      TraceIncludedInLog
        (openingInputTrace truncateSha256 (proof ordinal).position
          (.c1Leaf (proof ordinal).c1Value (proof ordinal).sharedSalt)
          (proof ordinal).c1Siblings) fullLog)
    (c2SuppliedCovered : ∀ ordinal : Fin disclosedQueryPairs,
      TraceIncludedInLog
        (openingInputTrace truncateSha256 (proof ordinal).position
          (.c2Leaf (proof ordinal).c2Value (proof ordinal).sharedSalt)
          (proof ordinal).c2Siblings) fullLog) :
    disclosuresAreProjections
        (extractPrefixFixedWords truncateSha256 prefixLog roots) proof ∨
      PrefixResolutionLateTargetHit truncateSha256 prefixLog fullLog roots
        proof ∨
      RawLogTruncatedDigestCollision truncateSha256 fullLog := by
  by_cases resolutionFailure : PrefixPathResolutionFailure truncateSha256
      prefixLog roots proof
  · rcases accepted_prefixResolutionFailure_yields_late_hit_or_collision
        truncateSha256 prefixLog fullLog roots proof accepted prefixIncluded
        c1SuppliedCovered c2SuppliedCovered resolutionFailure with
      lateHit | collision
    · exact Or.inr (Or.inl lateHit)
    · exact Or.inr (Or.inr collision)
  · by_cases collision : RawLogTruncatedDigestCollision truncateSha256 fullLog
    · exact Or.inr (Or.inr collision)
    · exact Or.inl (accepted_openings_are_prefix_fixed_projections
        truncateSha256 prefixLog fullLog roots proof accepted prefixIncluded
        resolutionFailure c1SuppliedCovered c2SuppliedCovered collision)

#print axioms resolveInput_none_excludes_matching_member
#print axioms authenticatingPath_of_bottomUpOpening
#print axioms acceptedC1Opening_yields_authenticatingPath
#print axioms acceptedC2Opening_yields_authenticatingPath
#print axioms firstUnresolvedTarget_yields_later_hit_or_collision
#print axioms accepted_prefixResolutionFailure_yields_late_hit_or_collision
#print axioms accepted_openings_yield_prefix_projections_or_late_hit_or_collision

end AspisPool.V7MerkleFirstUnresolvedBinding
