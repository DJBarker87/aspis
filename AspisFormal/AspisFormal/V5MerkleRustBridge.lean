import AspisFormal.V5MerkleAuthenticationBinding

/-!
# Source-shaped V5 private-opening bridge

This file expands the former whole-verifier correspondence premise into the
exact data flow of the two production helpers
`verify_v5_private_openings_from_proof` and
`verify_state_only_private_opening_from_proof_with_topology`.

The model records the five serialized sections, sorted and deduplicated index
sets, every `value || salt32` record, the level/parent/slot order of the shared
radix-four frontier, the final binary-cap sibling, and the exact bytes supplied
to SHA-256.  From one coherent shared execution it constructs all individual
paths required by `AcceptedV5Forest`.

No property of SHA-256 is proved here.  Uniqueness is conditional on the
explicit collision event below.  The final section names the remaining
source-extraction equality at the focused state-only helper; it is not used as
an axiom and is not hidden inside the deterministic theorems.
-/

namespace AspisV5MerkleRustBridge

open AspisV5MerkleAuthenticationBinding

abbrev Digest32 := Fin 32 -> Byte

def digestBytes (digest : Digest32) : List Byte :=
  List.ofFn digest

theorem digestBytes_length (digest : Digest32) :
    (digestBytes digest).length = 32 := by
  simp [digestBytes]

theorem digestBytes_injective : Function.Injective digestBytes := by
  intro left right heq
  exact List.ofFn_injective heq

theorem append_parts_eq_of_left_length_eq {A : Type*}
    {leftTail rightTail leftHead rightHead : List A}
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

/-! ## Exact SHA-256 inputs -/

/-- The byte string passed to the one logical SHA-256 invocation represented
by a Merkle call. -/
def hashInputBytes : HashCallInput Digest32 -> List Byte
  | .privateLeaf tag record => [0x10, tag] ++ record
  | .binaryNode left right =>
      [0x11] ++ digestBytes left ++ digestBytes right
  | .radix4Node children =>
      [0x12] ++ digestBytes (children 0) ++ digestBytes (children 1) ++
        digestBytes (children 2) ++ digestBytes (children 3)

theorem digestPairBytes_injective
    {left right left' right' : Digest32}
    (heq : digestBytes left ++ digestBytes right =
      digestBytes left' ++ digestBytes right') :
    left = left' ∧ right = right' := by
  obtain ⟨hleft, hright⟩ := append_parts_eq_of_left_length_eq
    (digestBytes_length left |>.trans (digestBytes_length left').symm) heq
  exact ⟨digestBytes_injective hleft, digestBytes_injective hright⟩

theorem digestFourBytes_injective
    {left right : Fin 4 -> Digest32}
    (heq : digestBytes (left 0) ++ digestBytes (left 1) ++
        digestBytes (left 2) ++ digestBytes (left 3) =
      digestBytes (right 0) ++ digestBytes (right 1) ++
        digestBytes (right 2) ++ digestBytes (right 3)) :
    left = right := by
  have split0 := append_parts_eq_of_left_length_eq
    (digestBytes_length (left 0) |>.trans (digestBytes_length (right 0)).symm)
    heq
  have split1 := append_parts_eq_of_left_length_eq
    (digestBytes_length (left 1) |>.trans (digestBytes_length (right 1)).symm)
    split0.2
  have split2 := digestPairBytes_injective split1.2
  have h0 := digestBytes_injective split0.1
  have h1 := digestBytes_injective split1.1
  have h2 := split2.1
  have h3 := split2.2
  funext slot
  fin_cases slot <;> assumption

theorem hashInputBytes_injective : Function.Injective hashInputBytes := by
  intro left right heq
  cases left with
  | privateLeaf leftTag leftRecord =>
      cases right with
      | privateLeaf rightTag rightRecord =>
          simp only [hashInputBytes, List.cons_append, List.nil_append] at heq
          injection heq with _hdomain htail
          injection htail with htag hrecord
          subst rightTag
          subst rightRecord
          rfl
      | binaryNode left right =>
          simp [hashInputBytes] at heq
      | radix4Node children =>
          simp [hashInputBytes] at heq
  | binaryNode leftDigest rightDigest =>
      cases right with
      | privateLeaf tag record =>
          simp [hashInputBytes] at heq
      | binaryNode leftDigest' rightDigest' =>
          change 0x11 :: (digestBytes leftDigest ++ digestBytes rightDigest) =
            0x11 :: (digestBytes leftDigest' ++ digestBytes rightDigest') at heq
          obtain ⟨hleft, hright⟩ := digestPairBytes_injective
            (List.cons.inj heq).2
          subst leftDigest'
          subst rightDigest'
          rfl
      | radix4Node children =>
          simp [hashInputBytes] at heq
  | radix4Node leftChildren =>
      cases right with
      | privateLeaf tag record =>
          simp [hashInputBytes] at heq
      | binaryNode left right =>
          simp [hashInputBytes] at heq
      | radix4Node rightChildren =>
          change 0x12 :: (digestBytes (leftChildren 0) ++
              digestBytes (leftChildren 1) ++ digestBytes (leftChildren 2) ++
                digestBytes (leftChildren 3)) =
            0x12 :: (digestBytes (rightChildren 0) ++
              digestBytes (rightChildren 1) ++ digestBytes (rightChildren 2) ++
                digestBytes (rightChildren 3)) at heq
          have hchildren := digestFourBytes_injective (List.cons.inj heq).2
          subst rightChildren
          rfl

/-- Instantiate the abstract Merkle interface with one SHA-256 byte-string
function.  Slice boundaries do not appear here because Rust's `hashv` hashes
their concatenation. -/
def sha256MerkleHashing (sha256 : List Byte -> Digest32) :
    MerkleHashing Digest32 where
  privateLeaf tag record := sha256 (hashInputBytes (.privateLeaf tag record))
  binaryNode left right := sha256 (hashInputBytes (.binaryNode left right))
  radix4Node children := sha256 (hashInputBytes (.radix4Node children))

theorem privateLeaf_hash_input (tag : Byte) (record : List Byte) :
    hashInputBytes (.privateLeaf tag record) = [0x10, tag] ++ record := rfl

theorem privateLeaf_hash_input_length (tag : Byte) (record : List Byte) :
    (hashInputBytes (.privateLeaf tag record)).length = 2 + record.length := by
  simp [hashInputBytes]
  omega

theorem binaryNode_hash_input (left right : Digest32) :
    hashInputBytes (.binaryNode left right) =
      [0x11] ++ digestBytes left ++ digestBytes right := rfl

theorem binaryNode_hash_input_length (left right : Digest32) :
    (hashInputBytes (.binaryNode left right)).length = 65 := by
  simp [hashInputBytes, digestBytes_length]

theorem radix4Node_hash_input (children : Fin 4 -> Digest32) :
    hashInputBytes (.radix4Node children) =
      [0x12] ++ digestBytes (children 0) ++ digestBytes (children 1) ++
        digestBytes (children 2) ++ digestBytes (children 3) := rfl

theorem radix4Node_hash_input_length (children : Fin 4 -> Digest32) :
    (hashInputBytes (.radix4Node children)).length = 129 := by
  simp [hashInputBytes, digestBytes_length]

theorem sha256_hashCall_eq (sha256 : List Byte -> Digest32)
    (call : HashCallInput Digest32) :
    hashCall (sha256MerkleHashing sha256) call = sha256 (hashInputBytes call) := by
  cases call <;> rfl

/-- The exact cryptographic failure event used by this bridge.  It only asks
for a collision between two distinct domain-separated Merkle calls actually
represented by the model. -/
def SHA256MerkleCollision (sha256 : List Byte -> Digest32) : Prop :=
  ∃ left right : HashCallInput Digest32,
    hashInputBytes left ≠ hashInputBytes right ∧
      sha256 (hashInputBytes left) = sha256 (hashInputBytes right)

theorem sha256MerkleCollision_iff_hashCollision
    (sha256 : List Byte -> Digest32) :
    SHA256MerkleCollision sha256 ↔
      HashCollision (sha256MerkleHashing sha256) := by
  constructor
  · rintro ⟨left, right, hbytes, heq⟩
    refine ⟨left, right, ?_, ?_⟩
    · intro hcalls
      exact hbytes (congrArg hashInputBytes hcalls)
    simpa only [sha256_hashCall_eq] using heq
  · rintro ⟨left, right, hcalls, heq⟩
    refine ⟨left, right, ?_, ?_⟩
    · intro hbytes
      exact hcalls (hashInputBytes_injective hbytes)
    simpa only [sha256_hashCall_eq] using heq

/-! ## Released routing and sorted/deduplicated topology -/

theorem released_section_indices (query : V5Query) :
    [sectionIndex .c1 query, sectionIndex .c2 query,
      sectionIndex .line1 query, sectionIndex .line2 query,
      sectionIndex .line3 query] =
      [query, query, query / 4, query / 16, query / 64] := rfl

theorem released_radix_level_counts :
    [radixLevelCount .c1, radixLevelCount .c2,
      radixLevelCount .line1, radixLevelCount .line2,
      radixLevelCount .line3] = [8, 8, 7, 6, 5] := rfl

theorem released_section_parameters :
    [(binaryDepth .c1, valueWidth .c1, (treeTag .c1).val),
      (binaryDepth .c2, valueWidth .c2, (treeTag .c2).val),
      (binaryDepth .line1, valueWidth .line1, (treeTag .line1).val),
      (binaryDepth .line2, valueWidth .line2, (treeTag .line2).val),
      (binaryDepth .line3, valueWidth .line3, (treeTag .line3).val)] =
      [(17, 256, 0x40), (17, 192, 0xc0), (15, 64, 0x41),
        (13, 64, 0x42), (11, 64, 0x43)] := rfl

theorem indexAtRadixLevel_eq_div_pow (index level : Nat) :
    indexAtRadixLevel index level = index / 4 ^ level := by
  induction level with
  | zero => simp [indexAtRadixLevel]
  | succ level ih =>
      rw [indexAtRadixLevel, ih, Nat.div_div_eq_div_mul, pow_succ]

theorem radixSlotsFromLevel_eq_range' (index level count : Nat) :
    radixSlotsFromLevel index level count =
      (List.range' level count).map fun currentLevel =>
        ⟨(index / 4 ^ currentLevel) % 4, Nat.mod_lt _ (by decide)⟩ := by
  induction count generalizing level with
  | zero => rfl
  | succ count ih =>
      simp only [radixSlotsFromLevel, List.range'_succ, List.map_cons,
        indexAtRadixLevel_eq_div_pow]
      rw [ih]

theorem radixSlots_eq_released_formula
    (tree : V5PrivateSection) (query : V5Query) :
    radixSlots tree query =
      (List.range (radixLevelCount tree)).map fun level =>
        ⟨(sectionIndex tree query / 4 ^ level) % 4,
          Nat.mod_lt _ (by decide)⟩ := by
  rw [radixSlots, radixSlotsFromLevel_eq_range']
  rw [← List.range_eq_range']

theorem binaryCapIndex_eq_released_formula
    (tree : V5PrivateSection) (query : V5Query) :
    binaryCapIndex tree query =
      sectionIndex tree query / 4 ^ radixLevelCount tree := by
  exact indexAtRadixLevel_eq_div_pow _ _

theorem sectionIndex_lt_leaf_count (tree : V5PrivateSection)
    (query : V5Query) : sectionIndex tree query < 2 ^ binaryDepth tree := by
  cases tree <;> simp [sectionIndex, binaryDepth] at * <;> omega

theorem binaryCapIndex_lt_two (tree : V5PrivateSection) (query : V5Query) :
    binaryCapIndex tree query < 2 := by
  cases tree <;>
    norm_num [binaryCapIndex, radixLevelCount, binaryDepth,
      indexAtRadixLevel, sectionIndex] at * <;> omega

/-- The set of indices held by Rust at a given radix level.  `level = 0` is
the leaf set; each successor divides every active index by four and deduplicates
the result. -/
def activeIndices (tree : V5PrivateSection) (queries : Finset V5Query)
    (level : Nat) : Finset Nat :=
  queries.image fun query =>
    indexAtRadixLevel (sectionIndex tree query) level

/-- Rust stores every level in increasing order.  `Finset.sort` expresses both
the sort and the deduplication performed by `derive_circle_line_query_indices`
and `Radix4BinaryCapTopology::new`. -/
def orderedActiveIndices (tree : V5PrivateSection)
    (queries : Finset V5Query) (level : Nat) : List Nat :=
  (activeIndices tree queries level).sort (.≤.)

theorem orderedActiveIndices_sorted (tree : V5PrivateSection)
    (queries : Finset V5Query) (level : Nat) :
    (orderedActiveIndices tree queries level).Pairwise (.≤.) := by
  exact Finset.pairwise_sort _ _

theorem orderedActiveIndices_nodup (tree : V5PrivateSection)
    (queries : Finset V5Query) (level : Nat) :
    (orderedActiveIndices tree queries level).Nodup := by
  exact Finset.sort_nodup _ _

theorem sectionIndex_mem_active (tree : V5PrivateSection)
    {queries : Finset V5Query} {query : V5Query} (hq : query ∈ queries) :
    sectionIndex tree query ∈ activeIndices tree queries 0 := by
  refine Finset.mem_image.mpr ⟨query, hq, ?_⟩
  rfl

structure FrontierPosition where
  level : Nat
  index : Nat
  deriving DecidableEq, Repr

def radixFrontierPositions (tree : V5PrivateSection)
    (queries : Finset V5Query) : List FrontierPosition :=
  (List.range (radixLevelCount tree)).flatMap fun level =>
    (orderedActiveIndices tree queries (level + 1)).flatMap fun parent =>
      ([0, 1, 2, 3].filter fun slot =>
        4 * parent + slot ∉ activeIndices tree queries level).map fun slot =>
          ⟨level, 4 * parent + slot⟩

/-- At the odd-depth cap Rust consumes no node when both top children are
active and otherwise consumes the absent child. -/
def binaryCapFrontierPositions (tree : V5PrivateSection)
    (queries : Finset V5Query) : List FrontierPosition :=
  ([0, 1].filter fun index =>
    index ∉ activeIndices tree queries (radixLevelCount tree)).map fun index =>
      ⟨radixLevelCount tree, index⟩

/-- Complete frontier order: radix levels from leaves upward, parents in
increasing order, slots `0,1,2,3`, then the optional binary-cap sibling. -/
def frontierPositions (tree : V5PrivateSection)
    (queries : Finset V5Query) : List FrontierPosition :=
  radixFrontierPositions tree queries ++
    binaryCapFrontierPositions tree queries

theorem frontierPositions_exact_order (tree : V5PrivateSection)
    (queries : Finset V5Query) :
    frontierPositions tree queries =
      (List.range (radixLevelCount tree)).flatMap (fun level =>
        (orderedActiveIndices tree queries (level + 1)).flatMap fun parent =>
          ([0, 1, 2, 3].filter fun slot =>
            4 * parent + slot ∉ activeIndices tree queries level).map
              fun slot => ⟨level, 4 * parent + slot⟩) ++
      ([0, 1].filter fun index =>
        index ∉ activeIndices tree queries (radixLevelCount tree)).map
          fun index => ⟨radixLevelCount tree, index⟩ := rfl

/-! ## Exact section wire grammar -/

def littleEndianByte (word place : Nat) : Byte :=
  ⟨(word / 256 ^ place) % 256, Nat.mod_lt _ (by decide)⟩

def u16LE (word : Nat) : List Byte :=
  [littleEndianByte word 0, littleEndianByte word 1]

def u32LE (word : Nat) : List Byte :=
  [littleEndianByte word 0, littleEndianByte word 1,
    littleEndianByte word 2, littleEndianByte word 3]

def encodePrivateSection (records : List (List Byte))
    (frontier : List Digest32) : List Byte :=
  u16LE records.length ++ records.flatten ++ u32LE frontier.length ++
    frontier.flatMap digestBytes

theorem u16LE_length (word : Nat) : (u16LE word).length = 2 := rfl

theorem u32LE_length (word : Nat) : (u32LE word).length = 4 := rfl

theorem encodePrivateSection_prefix (records : List (List Byte))
    (frontier : List Digest32) :
    encodePrivateSection records frontier =
      u16LE records.length ++ records.flatten ++ u32LE frontier.length ++
        frontier.flatMap digestBytes := rfl

theorem fixed_record_eq_value_append_salt {tree : V5PrivateSection}
    {record : List Byte} (_hlen : record.length = valueWidth tree + 32) :
    record = record.take (valueWidth tree) ++ record.drop (valueWidth tree) := by
  exact (List.take_append_drop (valueWidth tree) record).symm

theorem fixed_record_salt_length {tree : V5PrivateSection}
    {record : List Byte} (hlen : record.length = valueWidth tree + 32) :
    (record.drop (valueWidth tree)).length = 32 := by
  simp [List.length_drop, hlen]

/-! ## A source-shaped accepted section -/

/-- One successful shared-topology helper execution.  `node level index`
contains either a value derived from the record stream or the frontier value
consumed at that exact topology position.  The equations are precisely the
hash steps performed by the production loop. -/
structure ExactSectionTrace (sha256 : List Byte -> Digest32)
    (tree : V5PrivateSection) (root : Digest32)
    (queries : Finset V5Query) where
  wire : List Byte
  recordAt : Nat -> List Byte
  frontier : List Digest32
  node : Nat -> Nat -> Digest32
  records_length : ∀ index, index ∈ activeIndices tree queries 0 ->
    (recordAt index).length = valueWidth tree + 32
  wire_eq : wire = encodePrivateSection
    ((orderedActiveIndices tree queries 0).map recordAt) frontier
  frontier_eq : frontier =
    (frontierPositions tree queries).map fun position =>
      node position.level position.index
  leaf_eq : ∀ query, query ∈ queries ->
    node 0 (sectionIndex tree query) =
      (sha256MerkleHashing sha256).privateLeaf (treeTag tree)
        (recordAt (sectionIndex tree query))
  parent_eq : ∀ query, query ∈ queries -> ∀ level,
    level < radixLevelCount tree ->
    node (level + 1)
        (indexAtRadixLevel (sectionIndex tree query) (level + 1)) =
      (sha256MerkleHashing sha256).radix4Node fun slot =>
        node level
          (4 * indexAtRadixLevel (sectionIndex tree query) (level + 1) + slot)
  root_eq : (sha256MerkleHashing sha256).binaryNode
    (node (radixLevelCount tree) 0)
    (node (radixLevelCount tree) 1) = root

def ExactSectionTrace.records {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries) : List (List Byte) :=
  (orderedActiveIndices tree queries 0).map trace.recordAt

def ExactSectionTrace.values {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries) : List (List Byte) :=
  trace.records.map fun record => record.take (valueWidth tree)

theorem exactSection_wire_is_count_records_frontier
    {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries) :
    trace.wire = u16LE trace.records.length ++ trace.records.flatten ++
      u32LE trace.frontier.length ++ trace.frontier.flatMap digestBytes := by
  simpa [ExactSectionTrace.records, encodePrivateSection] using trace.wire_eq

theorem exactSection_frontier_has_no_omission_or_trailing
    {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries) :
    trace.frontier.length = (frontierPositions tree queries).length := by
  rw [trace.frontier_eq, List.length_map]

/-! ## Recovering every individual path from the shared execution -/

theorem fillChild_eq_self_of_eq {Digest : Type*} {slot : Fin 4}
    {children : Fin 4 -> Digest} {digest : Digest}
    (hslot : children slot = digest) :
    fillChild slot children digest = children := by
  funext other
  by_cases h : other = slot
  · subst other
    simp [fillChild, hslot]
  · simp [fillChild, Function.update, h]

theorem radix_index_recompose (index level : Nat) :
    4 * indexAtRadixLevel index (level + 1) +
        indexAtRadixLevel index level % 4 =
      indexAtRadixLevel index level := by
  rw [indexAtRadixLevel]
  have h := Nat.mod_add_div (indexAtRadixLevel index level) 4
  omega

/-- Authentication arrays for one query, projected from the shared node table.
At every level the queried slot is replaced by the running digest, exactly as
in `verify_radix4_binary_cap_with_matched_topology`. -/
def traceRadixWitnessAux {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (query : V5Query) (level : Nat) :
    (count : Nat) -> RadixWitness Digest32
      (radixSlotsFromLevel (sectionIndex tree query) level count)
  | 0 => .nil
  | count + 1 =>
      .cons
        (fun slot => trace.node level
          (4 * indexAtRadixLevel (sectionIndex tree query) (level + 1) + slot))
        (traceRadixWitnessAux trace query (level + 1) count)

theorem foldRadix_traceRadixWitnessAux {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (query : V5Query) (hq : query ∈ queries)
    (level count : Nat) (hbound : level + count ≤ radixLevelCount tree) :
    foldRadix (sha256MerkleHashing sha256)
        (traceRadixWitnessAux trace query level count)
        (trace.node level
          (indexAtRadixLevel (sectionIndex tree query) level)) =
      trace.node (level + count)
        (indexAtRadixLevel (sectionIndex tree query) (level + count)) := by
  induction count generalizing level with
  | zero =>
      rfl
  | succ count ih =>
      let slot : Fin 4 :=
        ⟨indexAtRadixLevel (sectionIndex tree query) level % 4,
          Nat.mod_lt _ (by decide)⟩
      let children : Fin 4 -> Digest32 := fun childSlot =>
        trace.node level
          (4 * indexAtRadixLevel (sectionIndex tree query) (level + 1) +
            childSlot)
      have hslot : children slot =
          trace.node level
            (indexAtRadixLevel (sectionIndex tree query) level) := by
        apply congrArg (trace.node level)
        exact radix_index_recompose (sectionIndex tree query) level
      have hfill : fillChild slot children
          (trace.node level
            (indexAtRadixLevel (sectionIndex tree query) level)) = children :=
        fillChild_eq_self_of_eq hslot
      have hlevel : level < radixLevelCount tree := by omega
      have hparent := trace.parent_eq query hq level hlevel
      change foldRadix (sha256MerkleHashing sha256)
          (traceRadixWitnessAux trace query (level + 1) count)
          ((sha256MerkleHashing sha256).radix4Node
            (fillChild slot children
              (trace.node level
                (indexAtRadixLevel (sectionIndex tree query) level)))) = _
      rw [hfill, ← hparent]
      have hrec := ih (level + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

def traceRadixWitness {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (query : V5Query) : RadixWitness Digest32 (radixSlots tree query) :=
  traceRadixWitnessAux trace query 0 (radixLevelCount tree)

def tracePath {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (query : V5Query) : OddBinaryCapPath Digest32 (radixSlots tree query) where
  radix := traceRadixWitness trace query
  topSibling :=
    if binaryCapIndex tree query = 0
    then trace.node (radixLevelCount tree) 1
    else trace.node (radixLevelCount tree) 0

theorem trace_foldRadix_eq_binaryCapNode {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (query : V5Query) (hq : query ∈ queries) :
    foldRadix (sha256MerkleHashing sha256) (traceRadixWitness trace query)
        ((sha256MerkleHashing sha256).privateLeaf (treeTag tree)
          (trace.recordAt (sectionIndex tree query))) =
      trace.node (radixLevelCount tree) (binaryCapIndex tree query) := by
  rw [← trace.leaf_eq query hq]
  change foldRadix (sha256MerkleHashing sha256)
      (traceRadixWitnessAux trace query 0 (radixLevelCount tree))
      (trace.node 0 (sectionIndex tree query)) =
    trace.node (radixLevelCount tree)
      (indexAtRadixLevel (sectionIndex tree query) (radixLevelCount tree))
  simpa only [indexAtRadixLevel, Nat.zero_add] using
    foldRadix_traceRadixWitnessAux trace query hq 0
      (radixLevelCount tree) (by omega)

theorem tracePath_root_eq {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (query : V5Query) (hq : query ∈ queries) :
    pathRoot (sha256MerkleHashing sha256) (topSide tree query)
        (tracePath trace query)
        ((sha256MerkleHashing sha256).privateLeaf (treeTag tree)
          (trace.recordAt (sectionIndex tree query))) = root := by
  change binaryCap (sha256MerkleHashing sha256) (topSide tree query)
      (foldRadix (sha256MerkleHashing sha256) (traceRadixWitness trace query)
        ((sha256MerkleHashing sha256).privateLeaf (treeTag tree)
          (trace.recordAt (sectionIndex tree query))))
      (if binaryCapIndex tree query = 0
        then trace.node (radixLevelCount tree) 1
        else trace.node (radixLevelCount tree) 0) = root
  rw [trace_foldRadix_eq_binaryCapNode trace query hq]
  have htop := binaryCapIndex_lt_two tree query
  have hcases : binaryCapIndex tree query = 0 ∨
      binaryCapIndex tree query = 1 := by omega
  rcases hcases with hzero | hone
  · simp [topSide, hzero, binaryCap, trace.root_eq]
  · simp [topSide, hone, binaryCap, trace.root_eq]

def ExactSectionTrace.acceptedLeaf {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (query : V5Query) (hq : query ∈ queries) :
    AcceptedV5Leaf (sha256MerkleHashing sha256) tree query root where
  record := trace.recordAt (sectionIndex tree query)
  record_length := trace.records_length _ (sectionIndex_mem_active tree hq)
  path := tracePath trace query
  root_eq := tracePath_root_eq trace query hq

def ExactSectionTrace.algebraicValue {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (query : V5Query) : List Byte :=
  (trace.recordAt (sectionIndex tree query)).take (valueWidth tree)

def ExactSectionTrace.salt {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (query : V5Query) : List Byte :=
  (trace.recordAt (sectionIndex tree query)).drop (valueWidth tree)

theorem exactSection_record_is_algebraicValue_append_salt
    {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (query : V5Query) (hq : query ∈ queries) :
    trace.recordAt (sectionIndex tree query) =
      trace.algebraicValue query ++ trace.salt query := by
  apply fixed_record_eq_value_append_salt
  exact trace.records_length _ (sectionIndex_mem_active tree hq)

theorem exactSection_salt_length {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (query : V5Query) (hq : query ∈ queries) :
    (trace.salt query).length = 32 := by
  apply fixed_record_salt_length
  exact trace.records_length _ (sectionIndex_mem_active tree hq)

theorem exactSection_algebraicValue_eq_openedValue
    {sha256 tree root queries}
    (trace : ExactSectionTrace sha256 tree root queries)
    (query : V5Query) (hq : query ∈ queries) :
    trace.algebraicValue query = openedValue (trace.acceptedLeaf query hq) := rfl

/-! ## Exact five-section helper composition -/

structure ExactV5Run (sha256 : List Byte -> Digest32)
    (roots : V5PrivateRoots Digest32) (queries : Finset V5Query) where
  proofBytes : List Byte
  query_count : queries.card = 18
  sections : ∀ tree, ExactSectionTrace sha256 tree (roots.get tree) queries
  proof_eq : proofBytes =
    (sections .c1).wire ++ (sections .c2).wire ++
      (sections .line1).wire ++ (sections .line2).wire ++
        (sections .line3).wire

theorem exactV5Run_five_section_order {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) :
    run.proofBytes =
      (run.sections .c1).wire ++ (run.sections .c2).wire ++
        (run.sections .line1).wire ++ (run.sections .line2).wire ++
          (run.sections .line3).wire :=
  run.proof_eq

def ExactV5Run.forest {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) :
    AcceptedV5Forest (sha256MerkleHashing sha256) roots queries where
  opening tree query hq := (run.sections tree).acceptedLeaf query hq

theorem exactV5Run_yieldsForest {sha256 roots queries}
    (run : ExactV5Run sha256 roots queries) :
    Nonempty (AcceptedV5Forest (sha256MerkleHashing sha256) roots queries) :=
  ⟨run.forest⟩

theorem exactV5Run_consumed_value_is_authenticated
    {sha256 roots queries} (run : ExactV5Run sha256 roots queries)
    (tree : V5PrivateSection) (query : V5Query) (hq : query ∈ queries) :
    (run.sections tree).algebraicValue query =
      openedValue (run.forest.opening tree query hq) := rfl

theorem exactV5Run_values_unique_outside_sha256_collision
    {sha256 roots queries}
    (hfree : ¬ SHA256MerkleCollision sha256)
    (left right : ExactV5Run sha256 roots queries)
    (tree : V5PrivateSection) (query : V5Query) (hq : query ∈ queries) :
    (left.sections tree).algebraicValue query =
      (right.sections tree).algebraicValue query := by
  rw [exactV5Run_consumed_value_is_authenticated left tree query hq,
    exactV5Run_consumed_value_is_authenticated right tree query hq]
  apply acceptedV5Forest_values_unique (sha256MerkleHashing sha256)
  simpa [CollisionFree, sha256MerkleCollision_iff_hashCollision] using hfree

/-! ## Narrow, explicit source-extraction boundary -/

/-- Arguments and returned remainder of one released-parameter call to
`verify_state_only_private_opening_from_proof_with_topology`.  The tree selects
the production depth, tag, width, and topology suffix; those are not supplied
as independently variable model inputs. -/
structure StateOnlyTopologyHelperCall where
  tree : V5PrivateSection
  root : Digest32
  queries : Finset V5Query
  proofBytes : List Byte
  remainder : List Byte

/-- Exact success condition for the focused state-only helper.  It consumes
one and only one encoded section from the front of `proofBytes` and returns the
literal suffix.  `ExactSectionTrace` supplies all parser projections and every
hash/frontier equation. -/
def ExactStateOnlyTopologyHelperAcceptance
    (sha256 : List Byte -> Digest32) (call : StateOnlyTopologyHelperCall) : Prop :=
  ∃ trace : ExactSectionTrace sha256 call.tree call.root call.queries,
    call.proofBytes = trace.wire ++ call.remainder

/-- The executable correspondence for the helper's boolean success and
returned remainder.  This relation does **not** expose the returned opening
slices.  `V5MerkleConsumedValueBridge` adds that stronger output relation and
binds the slices subsequently read by FRI.

This is a proposition to be discharged by focused Rust extraction.  It is not
an axiom and no theorem below assumes it silently. -/
def VerifyStateOnlyPrivateOpeningWithTopologySourceEquality
    (sha256 : List Byte -> Digest32)
    (rustHelperAccepts : StateOnlyTopologyHelperCall -> Prop) : Prop :=
  ∀ call, rustHelperAccepts call ↔
    ExactStateOnlyTopologyHelperAcceptance sha256 call

structure V5ProductionCall where
  roots : V5PrivateRoots Digest32
  queries : Finset V5Query
  proofBytes : List Byte

/-- Source-shaped success of the five-call driver.  In addition to the five
section traces, the exact proof byte string must be their concatenation, so a
sixth section, trailing byte, omitted frontier node, or reordered section is
outside this acceptance relation. -/
def ExactV5PrivateOpeningAcceptance (sha256 : List Byte -> Digest32)
    (call : V5ProductionCall) : Prop :=
  ∃ run : ExactV5Run sha256 call.roots call.queries,
    run.proofBytes = call.proofBytes

def stateOnlyCall (call : V5ProductionCall) (tree : V5PrivateSection)
    (proofBytes remainder : List Byte) : StateOnlyTopologyHelperCall where
  tree := tree
  root := call.roots.get tree
  queries := call.queries
  proofBytes := proofBytes
  remainder := remainder

/-- Literal source-shaped form of the five-iteration Rust driver.  Each call
receives the previous call's returned remainder; the fifth call must return an
empty remainder. -/
def V5DriverUsingStateOnlyHelper
    (rustHelperAccepts : StateOnlyTopologyHelperCall -> Prop)
    (call : V5ProductionCall) : Prop :=
  call.queries.card = 18 ∧
    ∃ afterC1 afterC2 afterLine1 afterLine2 : List Byte,
      rustHelperAccepts (stateOnlyCall call .c1 call.proofBytes afterC1) ∧
      rustHelperAccepts (stateOnlyCall call .c2 afterC1 afterC2) ∧
      rustHelperAccepts (stateOnlyCall call .line1 afterC2 afterLine1) ∧
      rustHelperAccepts (stateOnlyCall call .line2 afterLine1 afterLine2) ∧
      rustHelperAccepts (stateOnlyCall call .line3 afterLine2 [])

/-- Replacing the focused Rust helper by its exact model turns the literal
five-call driver into `ExactV5Run`.  This proof is the parser-remainder and
section-order composition that the old forest premise left implicit. -/
theorem helperSourceEquality_driver_iff_exactV5Acceptance
    (sha256 : List Byte -> Digest32)
    (rustHelperAccepts : StateOnlyTopologyHelperCall -> Prop)
    (hhelper : VerifyStateOnlyPrivateOpeningWithTopologySourceEquality
      sha256 rustHelperAccepts)
    (call : V5ProductionCall) :
    V5DriverUsingStateOnlyHelper rustHelperAccepts call ↔
      ExactV5PrivateOpeningAcceptance sha256 call := by
  constructor
  · rintro ⟨hcount, afterC1, afterC2, afterLine1, afterLine2,
      hc1, hc2, hline1, hline2, hline3⟩
    obtain ⟨c1, hc1bytes⟩ := (hhelper _).mp hc1
    obtain ⟨c2, hc2bytes⟩ := (hhelper _).mp hc2
    obtain ⟨line1, hline1bytes⟩ := (hhelper _).mp hline1
    obtain ⟨line2, hline2bytes⟩ := (hhelper _).mp hline2
    obtain ⟨line3, hline3bytes⟩ := (hhelper _).mp hline3
    change call.proofBytes = c1.wire ++ afterC1 at hc1bytes
    change afterC1 = c2.wire ++ afterC2 at hc2bytes
    change afterC2 = line1.wire ++ afterLine1 at hline1bytes
    change afterLine1 = line2.wire ++ afterLine2 at hline2bytes
    change afterLine2 = line3.wire ++ [] at hline3bytes
    let sections : ∀ tree,
        ExactSectionTrace sha256 tree (call.roots.get tree) call.queries :=
      fun tree => match tree with
        | .c1 => c1
        | .c2 => c2
        | .line1 => line1
        | .line2 => line2
        | .line3 => line3
    refine ⟨{
      proofBytes := call.proofBytes
      query_count := hcount
      sections := sections
      proof_eq := ?_ }, rfl⟩
    change call.proofBytes =
      c1.wire ++ c2.wire ++ line1.wire ++ line2.wire ++ line3.wire
    rw [hc1bytes, hc2bytes, hline1bytes, hline2bytes, hline3bytes]
    simp only [List.append_assoc, List.append_nil]
  · rintro ⟨run, hrun⟩
    let afterLine2 := (run.sections .line3).wire
    let afterLine1 := (run.sections .line2).wire ++ afterLine2
    let afterC2 := (run.sections .line1).wire ++ afterLine1
    let afterC1 := (run.sections .c2).wire ++ afterC2
    refine ⟨run.query_count, afterC1, afterC2, afterLine1, afterLine2,
      ?_, ?_, ?_, ?_, ?_⟩
    · apply (hhelper _).mpr
      refine ⟨run.sections .c1, ?_⟩
      change call.proofBytes = (run.sections .c1).wire ++ afterC1
      rw [← hrun, run.proof_eq]
      simp only [afterC1, afterC2, afterLine1, afterLine2, List.append_assoc]
    · apply (hhelper _).mpr
      exact ⟨run.sections .c2, rfl⟩
    · apply (hhelper _).mpr
      exact ⟨run.sections .line1, rfl⟩
    · apply (hhelper _).mpr
      exact ⟨run.sections .line2, rfl⟩
    · apply (hhelper _).mpr
      refine ⟨run.sections .line3, ?_⟩
      simp [stateOnlyCall, afterLine2]

/-- Shallow source equality for the Rust driver's control flow only.  All
Merkle semantics are delegated to the focused helper relation above. -/
def VerifyV5DriverCompositionSourceEquality
    (rustAccepts : V5ProductionCall -> Prop)
    (rustHelperAccepts : StateOnlyTopologyHelperCall -> Prop) : Prop :=
  ∀ call, rustAccepts call ↔
    V5DriverUsingStateOnlyHelper rustHelperAccepts call

/-- Exact equality still required between the public Rust driver and the
source-shaped composition.  Once the focused helper equality above is
extracted, this residual statement is the literal five-iteration call order
in `verify_v5_private_openings_from_proof`, followed by the empty-remainder
check in `verify_v5_private_openings`. -/
def VerifyV5PrivateOpeningsFromProofSourceEquality
    (sha256 : List Byte -> Digest32)
    (rustAccepts : V5ProductionCall -> Prop) : Prop :=
  ∀ call, rustAccepts call ↔ ExactV5PrivateOpeningAcceptance sha256 call

theorem focusedHelper_and_driver_source_equalities_imply_v5_sourceEquality
    (sha256 : List Byte -> Digest32)
    (rustAccepts : V5ProductionCall -> Prop)
    (rustHelperAccepts : StateOnlyTopologyHelperCall -> Prop)
    (hhelper : VerifyStateOnlyPrivateOpeningWithTopologySourceEquality
      sha256 rustHelperAccepts)
    (hdriver : VerifyV5DriverCompositionSourceEquality
      rustAccepts rustHelperAccepts) :
    VerifyV5PrivateOpeningsFromProofSourceEquality sha256 rustAccepts := by
  intro call
  rw [hdriver call,
    helperSourceEquality_driver_iff_exactV5Acceptance
      sha256 rustHelperAccepts hhelper call]

theorem exactV5PrivateOpeningAcceptance_yieldsForest
    (sha256 : List Byte -> Digest32) :
    RustAcceptedOpeningYieldsForest (sha256MerkleHashing sha256)
      (ExactV5PrivateOpeningAcceptance sha256)
      V5ProductionCall.roots V5ProductionCall.queries := by
  intro call haccept
  obtain ⟨run, _hbytes⟩ := haccept
  exact exactV5Run_yieldsForest run

/-- The old whole-verifier premise is now a consequence of one precisely
named source equality rather than an independent Merkle-security premise. -/
theorem verifyV5_sourceEquality_implies_RustAcceptedOpeningYieldsForest
    (sha256 : List Byte -> Digest32)
    (rustAccepts : V5ProductionCall -> Prop)
    (hsource : VerifyV5PrivateOpeningsFromProofSourceEquality sha256 rustAccepts) :
    RustAcceptedOpeningYieldsForest (sha256MerkleHashing sha256)
      rustAccepts V5ProductionCall.roots V5ProductionCall.queries := by
  intro call haccept
  exact exactV5PrivateOpeningAcceptance_yieldsForest sha256 call
    ((hsource call).mp haccept)

/-- For every production acceptance, outside the explicit SHA-256 event there
is an accepted production forest whose exposed values equal those in any
other accepted forest under the same roots and queries. -/
theorem productionAcceptedForest_values_unique
    (sha256 : List Byte -> Digest32)
    (rustAccepts : V5ProductionCall -> Prop)
    (hsource : VerifyV5PrivateOpeningsFromProofSourceEquality sha256 rustAccepts)
    (hfree : ¬ SHA256MerkleCollision sha256)
    (call : V5ProductionCall) (haccept : rustAccepts call) :
    ∃ production : AcceptedV5Forest (sha256MerkleHashing sha256)
        call.roots call.queries,
      ∀ other : AcceptedV5Forest (sha256MerkleHashing sha256)
          call.roots call.queries,
        ∀ tree query (hq : query ∈ call.queries),
          openedValue (production.opening tree query hq) =
            openedValue (other.opening tree query hq) := by
  have hforest :=
    verifyV5_sourceEquality_implies_RustAcceptedOpeningYieldsForest
      sha256 rustAccepts hsource call haccept
  obtain ⟨production⟩ := hforest
  refine ⟨production, ?_⟩
  intro other tree query hq
  apply acceptedV5Forest_values_unique (sha256MerkleHashing sha256)
  simpa [CollisionFree, sha256MerkleCollision_iff_hashCollision] using hfree

/-! ## Audit -/

#print axioms sha256MerkleCollision_iff_hashCollision
#print axioms hashInputBytes_injective
#print axioms foldRadix_traceRadixWitnessAux
#print axioms tracePath_root_eq
#print axioms exactSection_record_is_algebraicValue_append_salt
#print axioms exactV5Run_yieldsForest
#print axioms exactV5Run_values_unique_outside_sha256_collision
#print axioms helperSourceEquality_driver_iff_exactV5Acceptance
#print axioms focusedHelper_and_driver_source_equalities_imply_v5_sourceEquality
#print axioms verifyV5_sourceEquality_implies_RustAcceptedOpeningYieldsForest
#print axioms productionAcceptedForest_values_unique

end AspisV5MerkleRustBridge
