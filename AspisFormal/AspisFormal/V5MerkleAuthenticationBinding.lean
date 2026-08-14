import Mathlib

/-!
# Binding of the V5 private Merkle openings

The production V5 verifier authenticates five salted private trees.  Their
released parameters are, in order,

* C1: depth 17, 256 value bytes, tree tag `0x40`;
* C2: depth 17, 192 value bytes, tree tag `0xc0`;
* line 1: depth 15, 64 value bytes, tree tag `0x41`;
* line 2: depth 13, 64 value bytes, tree tag `0x42`; and
* line 3: depth 11, 64 value bytes, tree tag `0x43`.

Every opened record is `value || salt32`.  Rust hashes a leaf as
`SHA256(0x10 || tree_tag || record)`, a binary-cap node as
`SHA256(0x11 || left || right)`, and a radix-four node as
`SHA256(0x12 || child0 || child1 || child2 || child3)`.

This file does not assume that SHA-256 is collision resistant.  Instead it
defines the exact collision event needed by Merkle binding and proves the
deterministic implication: two different records accepted at the same tree,
root, and query index produce such a collision.  Therefore, outside that
explicit event, the C1, C2, and three later-layer values are unique.

The remaining implementation boundary is stated at the bottom: a successful
Rust radix-four/binary-cap multiproof must yield the per-leaf authentication
witness modeled here, using the same byte preimages and query-derived indices.
-/

namespace AspisV5MerkleAuthenticationBinding

abbrev Byte := Fin 256

/-! ## The three domain-separated SHA-256 call shapes -/

/-- The three kinds of primitive SHA-256 call made by the private tree.
The constructors represent the exact byte formats listed in the module
documentation. -/
inductive HashCallInput (Digest : Type*) where
  | privateLeaf (treeTag : Byte) (record : List Byte)
  | binaryNode (left right : Digest)
  | radix4Node (children : Fin 4 -> Digest)

/-- Abstract results of the exact primitive hash calls.  Instantiating these
functions with SHA-256 is an external implementation correspondence, not a
logical axiom. -/
structure MerkleHashing (Digest : Type*) where
  privateLeaf : Byte -> List Byte -> Digest
  binaryNode : Digest -> Digest -> Digest
  radix4Node : (Fin 4 -> Digest) -> Digest

def hashCall {Digest : Type*} (hashing : MerkleHashing Digest) :
    HashCallInput Digest -> Digest
  | .privateLeaf tag record => hashing.privateLeaf tag record
  | .binaryNode left right => hashing.binaryNode left right
  | .radix4Node children => hashing.radix4Node children

/-- The explicit external failure event: two different domain-separated
primitive hash calls return the same digest. -/
def HashCollision {Digest : Type*} (hashing : MerkleHashing Digest) : Prop :=
  ∃ left right : HashCallInput Digest,
    left ≠ right ∧ hashCall hashing left = hashCall hashing right

def CollisionFree {Digest : Type*} (hashing : MerkleHashing Digest) : Prop :=
  Not (HashCollision hashing)

/-! ## One radix-four path followed by the odd-depth binary cap -/

/-- Replace the queried child slot by the running digest.  Values supplied at
that slot by `siblings` are ignored. -/
def fillChild {Digest : Type*} (slot : Fin 4)
    (siblings : Fin 4 -> Digest) (digest : Digest) : Fin 4 -> Digest :=
  Function.update siblings slot digest

theorem fillChild_ne {Digest : Type*} {slot : Fin 4}
    {siblings1 siblings2 : Fin 4 -> Digest} {left right : Digest}
    (hne : left ≠ right) :
    fillChild slot siblings1 left ≠ fillChild slot siblings2 right := by
  intro heq
  have hat := congrFun heq slot
  exact hne (by simpa [fillChild] using hat)

/-- Authentication siblings for a fixed leaf-to-root list of radix-four
slots.  The slot list is determined by the public leaf index; two proofs may
supply different sibling digests but cannot change the slot order. -/
inductive RadixWitness (Digest : Type*) : List (Fin 4) -> Type _ where
  | nil : RadixWitness Digest []
  | cons {slot : Fin 4} {slots : List (Fin 4)}
      (siblings : Fin 4 -> Digest) (tail : RadixWitness Digest slots) :
      RadixWitness Digest (slot :: slots)

def foldRadix {Digest : Type*} (hashing : MerkleHashing Digest) :
    {slots : List (Fin 4)} -> RadixWitness Digest slots -> Digest -> Digest
  | [], .nil, digest => digest
  | slot :: slots, .cons siblings tail, digest =>
      foldRadix hashing tail
        (hashing.radix4Node (fillChild slot siblings digest))

/-- If different running digests become equal after radix-four paths with the
same public slot sequence, some radix-four compression call collided. -/
theorem foldRadix_collision_of_ne_of_eq {Digest : Type*}
    (hashing : MerkleHashing Digest) {slots : List (Fin 4)}
    (leftPath rightPath : RadixWitness Digest slots)
    {left right : Digest} (hne : left ≠ right)
    (heq : foldRadix hashing leftPath left =
      foldRadix hashing rightPath right) :
    HashCollision hashing := by
  induction slots generalizing left right with
  | nil =>
      cases leftPath
      cases rightPath
      exact (hne heq).elim
  | cons slot slots ih =>
      cases leftPath with
      | cons leftSiblings leftTail =>
        cases rightPath with
        | cons rightSiblings rightTail =>
          let leftChildren := fillChild slot leftSiblings left
          let rightChildren := fillChild slot rightSiblings right
          have hchildren : leftChildren ≠ rightChildren :=
            fillChild_ne hne
          by_cases hnode :
              hashing.radix4Node leftChildren =
                hashing.radix4Node rightChildren
          · refine ⟨.radix4Node leftChildren, .radix4Node rightChildren,
              ?_, hnode⟩
            intro hinput
            injection hinput with hchildrenEq
            exact hchildren hchildrenEq
          · apply ih leftTail rightTail hnode
            exact heq

inductive BinarySide where
  | left
  | right
  deriving DecidableEq

/-- One individual authentication path for an odd binary depth: radix-four
levels from the leaf upwards, then the final binary cap.  All five V5 private
trees have odd depth. -/
structure OddBinaryCapPath (Digest : Type*) (slots : List (Fin 4)) where
  radix : RadixWitness Digest slots
  topSibling : Digest

def binaryCap {Digest : Type*} (hashing : MerkleHashing Digest)
    (side : BinarySide) (digest sibling : Digest) : Digest :=
  match side with
  | .left => hashing.binaryNode digest sibling
  | .right => hashing.binaryNode sibling digest

def pathRoot {Digest : Type*} (hashing : MerkleHashing Digest)
    {slots : List (Fin 4)} (side : BinarySide)
    (path : OddBinaryCapPath Digest slots) (leafDigest : Digest) : Digest :=
  binaryCap hashing side (foldRadix hashing path.radix leafDigest)
    path.topSibling

/-- Different leaf digests accepted at the same public path geometry and root
force either a radix-four collision or a binary-cap collision.  The two proofs
may contain completely different sibling digests. -/
theorem pathRoot_collision_of_leaf_ne {Digest : Type*}
    (hashing : MerkleHashing Digest) {slots : List (Fin 4)}
    (side : BinarySide)
    (leftPath rightPath : OddBinaryCapPath Digest slots)
    {leftLeaf rightLeaf : Digest} (hleaf : leftLeaf ≠ rightLeaf)
    (hroot : pathRoot hashing side leftPath leftLeaf =
      pathRoot hashing side rightPath rightLeaf) :
    HashCollision hashing := by
  let leftTop := foldRadix hashing leftPath.radix leftLeaf
  let rightTop := foldRadix hashing rightPath.radix rightLeaf
  by_cases htop : leftTop = rightTop
  · exact foldRadix_collision_of_ne_of_eq hashing leftPath.radix
      rightPath.radix hleaf htop
  · cases side with
    | left =>
        refine ⟨.binaryNode leftTop leftPath.topSibling,
          .binaryNode rightTop rightPath.topSibling, ?_, ?_⟩
        · intro hinput
          injection hinput with hleft _hright
          exact htop hleft
        · exact hroot
    | right =>
        refine ⟨.binaryNode leftPath.topSibling leftTop,
          .binaryNode rightPath.topSibling rightTop, ?_, ?_⟩
        · intro hinput
          injection hinput with _hleft hright
          exact htop hright
        · exact hroot

/-! ## Exact V5 section parameters and query routing -/

inductive V5PrivateSection where
  | c1
  | c2
  | line1
  | line2
  | line3
  deriving DecidableEq, Fintype

def binaryDepth : V5PrivateSection -> Nat
  | .c1 => 17
  | .c2 => 17
  | .line1 => 15
  | .line2 => 13
  | .line3 => 11

def valueWidth : V5PrivateSection -> Nat
  | .c1 => 256
  | .c2 => 192
  | .line1 => 64
  | .line2 => 64
  | .line3 => 64

def treeTag : V5PrivateSection -> Byte
  | .c1 => 0x40
  | .c2 => 0xc0
  | .line1 => 0x41
  | .line2 => 0x42
  | .line3 => 0x43

abbrev V5Query := Fin 131072

/-- The five tree indices derived from one stored 17-bit query.  These are
Rust's `q`, `q`, `q >> 2`, `q >> 4`, and `q >> 6`. -/
def sectionIndex (tree : V5PrivateSection) (query : V5Query) : Nat :=
  match tree with
  | .c1 | .c2 => query
  | .line1 => query / 4
  | .line2 => query / 16
  | .line3 => query / 64

def radixLevelCount (tree : V5PrivateSection) : Nat :=
  binaryDepth tree / 2

/-- Repeated division by four.  At level `level` this is the integer index
stored by Rust's shared radix-four topology. -/
def indexAtRadixLevel (index : Nat) : Nat -> Nat
  | 0 => index
  | level + 1 => indexAtRadixLevel index level / 4

/-- The low two bits consumed at each radix-four level, written recursively
to expose the same state transition as the production loop. -/
def radixSlotsFromLevel (index level : Nat) : Nat -> List (Fin 4)
  | 0 => []
  | count + 1 =>
      ⟨indexAtRadixLevel index level % 4, Nat.mod_lt _ (by decide)⟩ ::
        radixSlotsFromLevel index (level + 1) count

/-- Leaf-to-root two-bit slots consumed by the radix-four levels. -/
def radixSlots (tree : V5PrivateSection) (query : V5Query) : List (Fin 4) :=
  radixSlotsFromLevel (sectionIndex tree query) 0 (radixLevelCount tree)

/-- Index of the node immediately below the final binary cap. -/
def binaryCapIndex (tree : V5PrivateSection) (query : V5Query) : Nat :=
  indexAtRadixLevel (sectionIndex tree query) (radixLevelCount tree)

/-- Orientation of the one remaining binary-cap bit. -/
def topSide (tree : V5PrivateSection) (query : V5Query) : BinarySide :=
  if binaryCapIndex tree query = 0 then .left else .right

theorem released_depths :
    [binaryDepth .c1, binaryDepth .c2, binaryDepth .line1,
      binaryDepth .line2, binaryDepth .line3] = [17, 17, 15, 13, 11] := rfl

theorem released_value_widths :
    [valueWidth .c1, valueWidth .c2, valueWidth .line1,
      valueWidth .line2, valueWidth .line3] = [256, 192, 64, 64, 64] := rfl

theorem released_tree_tags :
    [(treeTag .c1).val, (treeTag .c2).val, (treeTag .line1).val,
      (treeTag .line2).val, (treeTag .line3).val] =
      [0x40, 0xc0, 0x41, 0x42, 0x43] := rfl

theorem released_depths_are_odd (tree : V5PrivateSection) :
    binaryDepth tree % 2 = 1 := by
  cases tree <;> decide

/-! ## Accepted leaves and uniqueness outside the collision event -/

/-- Exact per-leaf data extracted from an accepted V5 opening.  Record length
includes the fixed 32-byte salt. -/
structure AcceptedV5Leaf {Digest : Type*} (hashing : MerkleHashing Digest)
    (tree : V5PrivateSection) (query : V5Query) (root : Digest) where
  record : List Byte
  record_length : record.length = valueWidth tree + 32
  path : OddBinaryCapPath Digest (radixSlots tree query)
  root_eq : pathRoot hashing (topSide tree query) path
      (hashing.privateLeaf (treeTag tree) record) = root

def openedValue {Digest : Type*} {hashing : MerkleHashing Digest}
    {tree : V5PrivateSection} {query : V5Query} {root : Digest}
    (opening : AcceptedV5Leaf hashing tree query root) : List Byte :=
  opening.record.take (valueWidth tree)

/-- Two different accepted records at one V5 section/query/root exhibit an
explicit primitive hash collision. -/
theorem acceptedV5Leaf_collision_of_record_ne {Digest : Type*}
    (hashing : MerkleHashing Digest) {tree : V5PrivateSection}
    {query : V5Query} {root : Digest}
    (left right : AcceptedV5Leaf hashing tree query root)
    (hne : left.record ≠ right.record) :
    HashCollision hashing := by
  let leftLeaf := hashing.privateLeaf (treeTag tree) left.record
  let rightLeaf := hashing.privateLeaf (treeTag tree) right.record
  by_cases hleaf : leftLeaf = rightLeaf
  · refine ⟨.privateLeaf (treeTag tree) left.record,
      .privateLeaf (treeTag tree) right.record, ?_, hleaf⟩
    intro hinput
    injection hinput with _htag hrecord
    exact hne hrecord
  · apply pathRoot_collision_of_leaf_ne hashing (topSide tree query)
      left.path right.path hleaf
    rw [left.root_eq, right.root_eq]

theorem acceptedV5Leaf_record_unique {Digest : Type*}
    (hashing : MerkleHashing Digest) (hfree : CollisionFree hashing)
    {tree : V5PrivateSection} {query : V5Query} {root : Digest}
    (left right : AcceptedV5Leaf hashing tree query root) :
    left.record = right.record := by
  by_contra hne
  exact hfree (acceptedV5Leaf_collision_of_record_ne hashing left right hne)

theorem acceptedV5Leaf_value_unique {Digest : Type*}
    (hashing : MerkleHashing Digest) (hfree : CollisionFree hashing)
    {tree : V5PrivateSection} {query : V5Query} {root : Digest}
    (left right : AcceptedV5Leaf hashing tree query root) :
    openedValue left = openedValue right := by
  rw [openedValue, openedValue,
    acceptedV5Leaf_record_unique hashing hfree left right]

structure V5PrivateRoots (Digest : Type*) where
  c1 : Digest
  c2 : Digest
  line1 : Digest
  line2 : Digest
  line3 : Digest

def V5PrivateRoots.get {Digest : Type*} (roots : V5PrivateRoots Digest) :
    V5PrivateSection -> Digest
  | .c1 => roots.c1
  | .c2 => roots.c2
  | .line1 => roots.line1
  | .line2 => roots.line2
  | .line3 => roots.line3

/-- Per-query path view of all five accepted private commitments.  The Rust
multiproof uses sorted/deduplicated index sets; this view repeats a shared
later-layer leaf for original queries with the same shifted index. -/
structure AcceptedV5Forest {Digest : Type*} (hashing : MerkleHashing Digest)
    (roots : V5PrivateRoots Digest) (queries : Finset V5Query) where
  opening : ∀ tree query, query ∈ queries ->
    AcceptedV5Leaf hashing tree query (roots.get tree)

/-- Outside the explicit hash-collision event, two accepted opening forests
under the same five roots and public queries expose exactly the same C1, C2,
and later-layer values. -/
theorem acceptedV5Forest_values_unique {Digest : Type*}
    (hashing : MerkleHashing Digest) (hfree : CollisionFree hashing)
    {roots : V5PrivateRoots Digest} {queries : Finset V5Query}
    (left right : AcceptedV5Forest hashing roots queries)
    (tree : V5PrivateSection) (query : V5Query) (hq : query ∈ queries) :
    openedValue (left.opening tree query hq) =
      openedValue (right.opening tree query hq) :=
  acceptedV5Leaf_value_unique hashing hfree
    (left.opening tree query hq) (right.opening tree query hq)

/-! ## Exact remaining Rust-to-model boundary -/

/-- A successful call to the production V5 opening verifier yields the five
per-leaf paths above.  This proposition is deliberately only a name for the
remaining source-correspondence task.  It does not assume collision resistance
and is not used to prove any theorem in this file.

Concretely, the missing proof must connect
`verify_v5_private_openings_from_proof` and
`verify_state_only_private_opening_from_proof_with_topology` to this model,
including parser slices, `value || salt32`, the shared shifted-index topology,
frontier consumption order, the odd-depth binary cap, and the three exact
domain-separated SHA-256 call formats. -/
def RustAcceptedOpeningYieldsForest
    {RustInput Digest : Type*} (hashing : MerkleHashing Digest)
    (rustAccepts : RustInput -> Prop)
    (rootsOf : RustInput -> V5PrivateRoots Digest)
    (queriesOf : RustInput -> Finset V5Query) : Prop :=
  ∀ input, rustAccepts input ->
    Nonempty (AcceptedV5Forest hashing (rootsOf input) (queriesOf input))

/-! ## Audit -/

#print axioms foldRadix_collision_of_ne_of_eq
#print axioms pathRoot_collision_of_leaf_ne
#print axioms acceptedV5Leaf_collision_of_record_ne
#print axioms acceptedV5Leaf_record_unique
#print axioms acceptedV5Forest_values_unique

end AspisV5MerkleAuthenticationBinding
