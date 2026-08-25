import Mathlib

/-!
# Exact Tag-73 two-tree Merkle query grammar

This module freezes the byte strings supplied to SHA-256 by the deployed V7
private-opening verifier.  It is the grammar layer for the K1.2 ordered-query
extractor; it does not assign a random-oracle probability or claim complete
witness extraction.

The authenticated digests are the first 26 SHA-256 bytes.  C1 and C2 share one
oracle log, but their leaf tags and widths are distinct:

* C1: `0x10 || 0x71 || value[403] || salt[32]`;
* C2: `0x10 || 0xf1 || value[186] || salt[32]`;
* node: `0x11 || left[26] || right[26]`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisPool.V7MerkleQueryGrammar

abbrev Byte := Fin 256
abbrev Digest208 := Fin 26 → Byte
abbrev C1Value := Fin 403 → Byte
abbrev C2Value := Fin 186 → Byte
abbrev Salt32 := Fin 32 → Byte

def treeDepth : Nat := 18
def disclosedQueryPairs : Nat := 16

theorem frozen_tree_parameters :
    treeDepth = 18 ∧ disclosedQueryPairs = 16 := by
  norm_num [treeDepth, disclosedQueryPairs]

def fixedBytes {n : Nat} (value : Fin n → Byte) : List Byte :=
  List.ofFn value

@[simp] theorem fixedBytes_length {n : Nat} (value : Fin n → Byte) :
    (fixedBytes value).length = n := by
  simp [fixedBytes]

theorem fixedBytes_injective {n : Nat} :
    Function.Injective (fixedBytes : (Fin n → Byte) → List Byte) := by
  intro left right heq
  exact List.ofFn_injective heq

theorem append_parts_eq_of_left_length_eq {A : Type*}
    {leftHead rightHead leftTail rightTail : List A}
    (hlen : leftHead.length = rightHead.length)
    (heq : leftHead ++ leftTail = rightHead ++ rightTail) :
    leftHead = rightHead ∧ leftTail = rightTail := by
  constructor
  · calc
      leftHead = (leftHead ++ leftTail).take leftHead.length := by simp
      _ = (rightHead ++ rightTail).take leftHead.length := by rw [heq]
      _ = rightHead := by rw [hlen]; simp
  · calc
      leftTail = (leftHead ++ leftTail).drop leftHead.length := by simp
      _ = (rightHead ++ rightTail).drop leftHead.length := by rw [heq]
      _ = rightTail := by rw [hlen]; simp

/-- Every well-typed SHA-256 input used by the two V7 commitment trees. -/
inductive TypedPreimage where
  | c1Leaf (value : C1Value) (salt : Salt32)
  | c2Leaf (value : C2Value) (salt : Salt32)
  | node (left right : Digest208)
  deriving DecidableEq

/-- Exact concatenated bytes passed to SHA-256. -/
def serialize : TypedPreimage → List Byte
  | .c1Leaf value salt => [0x10, 0x71] ++ fixedBytes value ++ fixedBytes salt
  | .c2Leaf value salt => [0x10, 0xf1] ++ fixedBytes value ++ fixedBytes salt
  | .node left right => [0x11] ++ fixedBytes left ++ fixedBytes right

@[simp] theorem serialize_c1_length (value : C1Value) (salt : Salt32) :
    (serialize (.c1Leaf value salt)).length = 437 := by
  simp [serialize]

@[simp] theorem serialize_c2_length (value : C2Value) (salt : Salt32) :
    (serialize (.c2Leaf value salt)).length = 220 := by
  simp [serialize]

@[simp] theorem serialize_node_length (left right : Digest208) :
    (serialize (.node left right)).length = 53 := by
  simp [serialize]

theorem serialize_length : ∀ input : TypedPreimage,
    (serialize input).length = match input with
      | .c1Leaf _ _ => 437
      | .c2Leaf _ _ => 220
      | .node _ _ => 53
  := by
  intro input
  cases input <;> simp

/-- Domain tags and fixed widths make the exact serialization injective.  In
particular a C1 leaf, C2 leaf, and internal node can never be confused by the
byte parser before hashing. -/
theorem serialize_injective : Function.Injective serialize := by
  intro left right heq
  cases left with
  | c1Leaf leftValue leftSalt =>
      cases right with
      | c1Leaf rightValue rightSalt =>
          have htail :
              fixedBytes leftValue ++ fixedBytes leftSalt =
                fixedBytes rightValue ++ fixedBytes rightSalt := by
            change (0x10 : Byte) :: 0x71 ::
                (fixedBytes leftValue ++ fixedBytes leftSalt) =
              0x10 :: 0x71 ::
                (fixedBytes rightValue ++ fixedBytes rightSalt) at heq
            exact (List.cons.inj (List.cons.inj heq).2).2
          obtain ⟨hvalue, hsalt⟩ := append_parts_eq_of_left_length_eq
            (fixedBytes_length leftValue |>.trans
              (fixedBytes_length rightValue).symm) htail
          have := fixedBytes_injective hvalue
          have := fixedBytes_injective hsalt
          subst rightValue
          subst rightSalt
          rfl
      | c2Leaf rightValue rightSalt =>
          simp [serialize] at heq
      | node rightLeft rightRight =>
          simp [serialize] at heq
  | c2Leaf leftValue leftSalt =>
      cases right with
      | c1Leaf rightValue rightSalt =>
          simp [serialize] at heq
      | c2Leaf rightValue rightSalt =>
          have htail :
              fixedBytes leftValue ++ fixedBytes leftSalt =
                fixedBytes rightValue ++ fixedBytes rightSalt := by
            change (0x10 : Byte) :: 0xf1 ::
                (fixedBytes leftValue ++ fixedBytes leftSalt) =
              0x10 :: 0xf1 ::
                (fixedBytes rightValue ++ fixedBytes rightSalt) at heq
            exact (List.cons.inj (List.cons.inj heq).2).2
          obtain ⟨hvalue, hsalt⟩ := append_parts_eq_of_left_length_eq
            (fixedBytes_length leftValue |>.trans
              (fixedBytes_length rightValue).symm) htail
          have := fixedBytes_injective hvalue
          have := fixedBytes_injective hsalt
          subst rightValue
          subst rightSalt
          rfl
      | node rightLeft rightRight =>
          simp [serialize] at heq
  | node leftLeft leftRight =>
      cases right with
      | c1Leaf rightValue rightSalt =>
          simp [serialize] at heq
      | c2Leaf rightValue rightSalt =>
          simp [serialize] at heq
      | node rightLeft rightRight =>
          have htail :
              fixedBytes leftLeft ++ fixedBytes leftRight =
                fixedBytes rightLeft ++ fixedBytes rightRight := by
            change (0x11 : Byte) ::
                (fixedBytes leftLeft ++ fixedBytes leftRight) =
              0x11 :: (fixedBytes rightLeft ++ fixedBytes rightRight) at heq
            exact (List.cons.inj heq).2
          obtain ⟨hleft, hright⟩ := append_parts_eq_of_left_length_eq
            (fixedBytes_length leftLeft |>.trans
              (fixedBytes_length rightLeft).symm) htail
          have := fixedBytes_injective hleft
          have := fixedBytes_injective hright
          subst rightLeft
          subst rightRight
          rfl

/-- A 208-bit-prefix collision across the *combined* C1/C2/node grammar.  The
quantification is intentionally not split into two independent trees. -/
def TruncatedDigestCollision
    (truncateSha256 : List Byte → Digest208) : Prop :=
  ∃ left right : TypedPreimage,
    left ≠ right ∧
      truncateSha256 (serialize left) = truncateSha256 (serialize right)

theorem truncatedDigestCollision_iff_serialized_collision
    (truncateSha256 : List Byte → Digest208) :
    TruncatedDigestCollision truncateSha256 ↔
      ∃ left right : TypedPreimage,
        serialize left ≠ serialize right ∧
          truncateSha256 (serialize left) =
            truncateSha256 (serialize right) := by
  constructor
  · rintro ⟨left, right, hne, heq⟩
    exact ⟨left, right, fun hbytes => hne (serialize_injective hbytes), heq⟩
  · rintro ⟨left, right, hbytes, heq⟩
    exact ⟨left, right, fun hsame => hbytes (congrArg serialize hsame), heq⟩

/-! ## One combined ordered raw-oracle log

Malformed inputs are not parsed as tree vertices, but they remain in this raw
log and therefore participate in the same truncated-prefix collision event.
The resolver always chooses the first matching answer.  A child reference is
classified relative to the parent's query index, so a later answer cannot be
silently treated as causal.
-/

abbrev RawHashInput := List Byte
abbrev OrderedRawQueryLog := List RawHashInput

/-- Collision event across every distinct raw input in the shared log,
including inputs that do not parse as one of the three typed tree forms. -/
def RawLogTruncatedDigestCollision
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) : Prop :=
  ∃ left ∈ log, ∃ right ∈ log,
    left ≠ right ∧ truncateSha256 left = truncateSha256 right

/-- Find the first query in `inputs` whose 208-bit answer is `target`, adding
`offset` to the returned local index. -/
def resolveFirstAux (truncateSha256 : RawHashInput → Digest208)
    (target : Digest208) : Nat → OrderedRawQueryLog → Option Nat
  | _, [] => none
  | offset, input :: rest =>
      if truncateSha256 input = target then some offset
      else resolveFirstAux truncateSha256 target (offset + 1) rest

def resolveFirst (truncateSha256 : RawHashInput → Digest208)
    (target : Digest208) (log : OrderedRawQueryLog) : Option Nat :=
  resolveFirstAux truncateSha256 target 0 log

inductive ReferenceResolution where
  /-- The child preimage was queried before its parent. -/
  | earlier (queryIndex : Nat)
  /-- The first matching answer occurs at or after the parent query. -/
  | forward (queryIndex : Nat)
  /-- No query in the recorded log has the referenced answer. -/
  | missing
  deriving DecidableEq, Repr

/-- Resolve a child digest against the ordered shared log.  The prefix before
`parentQueryIndex` is searched first; only if it has no match is the suffix
searched and reported as a forward reference. -/
def classifyReference (truncateSha256 : RawHashInput → Digest208)
    (target : Digest208) (parentQueryIndex : Nat)
    (log : OrderedRawQueryLog) : ReferenceResolution :=
  match resolveFirstAux truncateSha256 target 0
      (log.take parentQueryIndex) with
  | some index => .earlier index
  | none =>
      match resolveFirstAux truncateSha256 target parentQueryIndex
          (log.drop parentQueryIndex) with
      | some index => .forward index
      | none => .missing

@[simp] theorem resolveFirstAux_nil
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208)
    (offset : Nat) :
    resolveFirstAux truncateSha256 target offset [] = none := rfl

theorem resolveFirstAux_cons_match
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208)
    (offset : Nat) (input : RawHashInput) (rest : OrderedRawQueryLog)
    (answer : truncateSha256 input = target) :
    resolveFirstAux truncateSha256 target offset (input :: rest) =
      some offset := by
  simp [resolveFirstAux, answer]

theorem resolveFirstAux_cons_miss
    (truncateSha256 : RawHashInput → Digest208) (target : Digest208)
    (offset : Nat) (input : RawHashInput) (rest : OrderedRawQueryLog)
    (answer : truncateSha256 input ≠ target) :
    resolveFirstAux truncateSha256 target offset (input :: rest) =
      resolveFirstAux truncateSha256 target (offset + 1) rest := by
  simp [resolveFirstAux, answer]

#print axioms serialize_injective
#print axioms truncatedDigestCollision_iff_serialized_collision
#print axioms frozen_tree_parameters
#print axioms resolveFirstAux_cons_match
#print axioms resolveFirstAux_cons_miss

end AspisPool.V7MerkleQueryGrammar
