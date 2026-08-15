import AspisFormal.V5MerkleRustBridge

/-!
# The index plan shared by the five V5 private Merkle openings

The production verifier builds one radix-four index plan from the layer-zero
query indices and reuses successive suffixes for the three later FRI layers.
This file states that plan without hashes and proves the arithmetic facts that
make the reuse valid:

* every next level is exactly division by four followed by deduplication;
* every stored parent has exactly the child slots present at the prior level;
* the later-layer index lists are literally levels one, two, and three of the
  layer-zero plan; and
* flattening all level and mask lists with prefix-sum offsets returns the exact
  list for each requested level.

The remaining implementation obligation is deliberately smaller than the old
whole-helper equality: extraction must show that
`Radix4BinaryCapTopology::new` constructs this hash-free plan.  The already
extracted `level_indices`, `group_masks`, and `matched_suffix` methods then
show that successful production reads return literal stored slices.
-/

namespace AspisV5TopologyConstruction

open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge

/-- The shared plan is built from the C1/layer-zero indices. -/
def sharedActiveIndices (queries : Finset V5Query) (level : Nat) : Finset Nat :=
  activeIndices .c1 queries level

/-- The exact sorted, deduplicated list stored for one shared-plan level. -/
def sharedLevelIndices (queries : Finset V5Query) (level : Nat) : List Nat :=
  orderedActiveIndices .c1 queries level

theorem activeIndices_succ (tree : V5PrivateSection)
    (queries : Finset V5Query) (level : Nat) :
    activeIndices tree queries (level + 1) =
      (activeIndices tree queries level).image fun index => index / 4 := by
  ext parent
  simp only [activeIndices, Finset.mem_image]
  constructor
  · rintro ⟨query, hquery, hparent⟩
    refine ⟨indexAtRadixLevel (sectionIndex tree query) level, ?_, ?_⟩
    · exact ⟨query, hquery, rfl⟩
    · simpa only [indexAtRadixLevel] using hparent
  · rintro ⟨index, ⟨query, hquery, rfl⟩, hparent⟩
    exact ⟨query, hquery, by simpa only [indexAtRadixLevel] using hparent⟩

theorem sharedActiveIndices_succ (queries : Finset V5Query) (level : Nat) :
    sharedActiveIndices queries (level + 1) =
      (sharedActiveIndices queries level).image fun index => index / 4 := by
  exact activeIndices_succ .c1 queries level

/-- Child slots which are already supplied by the active nodes below one
parent.  The complement is exactly the frontier order consumed by Rust. -/
def presentSlots (queries : Finset V5Query) (level parent : Nat) :
    Finset (Fin 4) :=
  Finset.univ.filter fun slot =>
    4 * parent + slot.val ∈ sharedActiveIndices queries level

@[simp] theorem mem_presentSlots_iff (queries : Finset V5Query)
    (level parent : Nat) (slot : Fin 4) :
    slot ∈ presentSlots queries level parent ↔
      4 * parent + slot.val ∈ sharedActiveIndices queries level := by
  simp [presentSlots]

theorem parent_mem_next_iff_presentSlot_nonempty
    (queries : Finset V5Query) (level parent : Nat) :
    parent ∈ sharedActiveIndices queries (level + 1) ↔
      (presentSlots queries level parent).Nonempty := by
  rw [sharedActiveIndices_succ]
  constructor
  · intro hmembership
    obtain ⟨index, hindex, hparent⟩ := Finset.mem_image.mp hmembership
    let slot : Fin 4 := ⟨index % 4, Nat.mod_lt _ (by decide)⟩
    refine ⟨slot, ?_⟩
    rw [mem_presentSlots_iff]
    have hdecompose := Nat.mod_add_div index 4
    have : 4 * parent + index % 4 = index := by omega
    simpa [slot, this] using hindex
  · rintro ⟨slot, hslot⟩
    refine Finset.mem_image.mpr ⟨4 * parent + slot.val, ?_, ?_⟩
    · exact (mem_presentSlots_iff queries level parent slot).mp hslot
    · have hslotBound : slot.val < 4 := slot.isLt
      omega

/-- The child-slot sets in the exact parent order used by the shared plan. -/
def sharedGroupSlots (queries : Finset V5Query) (level : Nat) :
    List (Finset (Fin 4)) :=
  (sharedLevelIndices queries (level + 1)).map
    (presentSlots queries level)

/-- The literal low-four-bit mask stored by Rust for one parent. -/
def slotMask (slots : Finset (Fin 4)) : Nat :=
  ∑ slot ∈ slots, 2 ^ slot.val

def sharedGroupMasks (queries : Finset V5Query) (level : Nat) : List Nat :=
  (sharedGroupSlots queries level).map slotMask

theorem slotMask_lt_sixteen (slots : Finset (Fin 4)) :
    slotMask slots < 16 := by
  have hle : slotMask slots ≤ ∑ slot : Fin 4, 2 ^ slot.val := by
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ slots)
  rw [Fin.sum_univ_four] at hle
  norm_num at hle
  omega

theorem every_shared_group_is_nonempty (queries : Finset V5Query)
    (level : Nat) (slots : Finset (Fin 4))
    (hslots : slots ∈ sharedGroupSlots queries level) : slots.Nonempty := by
  simp only [sharedGroupSlots, List.mem_map] at hslots
  obtain ⟨parent, hparent, rfl⟩ := hslots
  apply (parent_mem_next_iff_presentSlot_nonempty queries level parent).mp
  exact (Finset.mem_sort (· ≤ ·)).mp hparent

theorem shared_group_slot_is_exact (queries : Finset V5Query)
    (level parent : Nat)
    (_hparent : parent ∈ sharedLevelIndices queries (level + 1))
    (slot : Fin 4) :
    slot ∈ presentSlots queries level parent ↔
      4 * parent + slot.val ∈ sharedLevelIndices queries level := by
  rw [mem_presentSlots_iff]
  exact (Finset.mem_sort (· ≤ ·)).symm

/-! ## The three reused suffixes -/

theorem line1_indices_are_shared_level_one (queries : Finset V5Query) :
    orderedActiveIndices .line1 queries 0 = sharedLevelIndices queries 1 := by
  rfl

theorem line2_indices_are_shared_level_two (queries : Finset V5Query) :
    orderedActiveIndices .line2 queries 0 = sharedLevelIndices queries 2 := by
  unfold orderedActiveIndices sharedLevelIndices
  congr 1
  ext index
  simp [activeIndices, sectionIndex,
    indexAtRadixLevel, Nat.div_div_eq_div_mul]

theorem line3_indices_are_shared_level_three (queries : Finset V5Query) :
    orderedActiveIndices .line3 queries 0 = sharedLevelIndices queries 3 := by
  unfold orderedActiveIndices sharedLevelIndices
  congr 1
  ext index
  simp [activeIndices, sectionIndex,
    indexAtRadixLevel, Nat.div_div_eq_div_mul]

theorem c2_indices_are_shared_level_zero (queries : Finset V5Query) :
    orderedActiveIndices .c2 queries 0 = sharedLevelIndices queries 0 := by
  rfl

theorem released_section_indices_are_exact_shared_suffixes
    (queries : Finset V5Query) :
    [orderedActiveIndices .c1 queries 0,
      orderedActiveIndices .c2 queries 0,
      orderedActiveIndices .line1 queries 0,
      orderedActiveIndices .line2 queries 0,
      orderedActiveIndices .line3 queries 0] =
    [sharedLevelIndices queries 0,
      sharedLevelIndices queries 0,
      sharedLevelIndices queries 1,
      sharedLevelIndices queries 2,
      sharedLevelIndices queries 3] := by
  simp [sharedLevelIndices, line1_indices_are_shared_level_one,
    line2_indices_are_shared_level_two, line3_indices_are_shared_level_three,
    c2_indices_are_shared_level_zero]

theorem released_section_depths_are_shared_suffix_depths :
    [binaryDepth .c1, binaryDepth .c2, binaryDepth .line1,
      binaryDepth .line2, binaryDepth .line3] =
    [17 - 2 * 0, 17 - 2 * 0, 17 - 2 * 1,
      17 - 2 * 2, 17 - 2 * 3] := by
  decide

/-! ## The flattened vectors and their offsets -/

/-- Nine stored index levels, from the leaves through the last radix-four
parent level of the released depth-17 tree. -/
def sharedLevelLists (queries : Finset V5Query) : List (List Nat) :=
  (List.range 9).map (sharedLevelIndices queries)

/-- Eight stored group-mask levels, one for each radix-four transition. -/
def sharedGroupLists (queries : Finset V5Query) :
    List (List (Finset (Fin 4))) :=
  (List.range 8).map (sharedGroupSlots queries)

def prefixOffset (lists : List (List α)) (level : Nat) : Nat :=
  ((lists.map List.length).take level).sum

theorem flatten_slice_at {lists : List (List α)} {level : Nat}
    (hlevel : level < lists.length) :
    (lists.flatten.drop (prefixOffset lists level)).take
        lists[level].length = lists[level] := by
  rw [prefixOffset, List.drop_sum_flatten]
  rw [List.drop_eq_getElem_cons hlevel, List.flatten_cons]
  rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]

theorem sharedLevelLists_get (queries : Finset V5Query) (level : Nat)
    (hlevel : level < 9) :
    (sharedLevelLists queries)[level] = sharedLevelIndices queries level := by
  simp [sharedLevelLists]

theorem sharedGroupLists_get (queries : Finset V5Query) (level : Nat)
    (hlevel : level < 8) :
    (sharedGroupLists queries)[level] = sharedGroupSlots queries level := by
  simp [sharedGroupLists]

theorem flattened_level_slice_is_exact (queries : Finset V5Query)
    (level : Nat) (hlevel : level < 9) :
    ((sharedLevelLists queries).flatten.drop
        (prefixOffset (sharedLevelLists queries) level)).take
          (sharedLevelIndices queries level).length =
      sharedLevelIndices queries level := by
  have hlength : (sharedLevelLists queries).length = 9 := by
    simp [sharedLevelLists]
  have hslice := flatten_slice_at
    (lists := sharedLevelLists queries) (level := level) (by omega)
  rw [← sharedLevelLists_get queries level hlevel]
  exact hslice

theorem flattened_group_slice_is_exact (queries : Finset V5Query)
    (level : Nat) (hlevel : level < 8) :
    ((sharedGroupLists queries).flatten.drop
        (prefixOffset (sharedGroupLists queries) level)).take
          (sharedGroupSlots queries level).length =
      sharedGroupSlots queries level := by
  have hlength : (sharedGroupLists queries).length = 8 := by
    simp [sharedGroupLists]
  have hslice := flatten_slice_at
    (lists := sharedGroupLists queries) (level := level) (by omega)
  rw [← sharedGroupLists_get queries level hlevel]
  exact hslice

/-! ## Precisely split residual implementation obligations -/

/-- Hash-free observation returned by a successful topology construction. -/
structure TopologyObservation where
  levelIndices : Nat -> List Nat
  groupMasks : Nat -> List Nat
  binaryDepth : Nat
  radixLevels : Nat

def exactTopologyObservation (queries : Finset V5Query) :
    TopologyObservation where
  levelIndices := sharedLevelIndices queries
  groupMasks := sharedGroupMasks queries
  binaryDepth := 17
  radixLevels := 8

/-- Remaining source equality for the constructor alone, restricted to the
released eighteen-query calls.  It no longer contains parser, SHA-256,
frontier consumption, or root comparison behavior. -/
def Radix4BinaryCapTopologyNewSourceEquality
    (rustConstructs : Finset V5Query -> Option TopologyObservation) : Prop :=
  ∀ queries, queries.card = 18 ->
    rustConstructs queries = some (exactTopologyObservation queries)

/-- Exact released-call helper equality.  Requiring only calls with eighteen
queries is sufficient for the five-section production driver. -/
def VerifyStateOnlyPrivateOpeningWithTopologyReleasedSourceEquality
    (sha256 : List Byte -> Digest32)
    (rustHelperAccepts : StateOnlyTopologyHelperCall -> Prop) : Prop :=
  ∀ call, call.queries.card = 18 ->
    (rustHelperAccepts call ↔
      ExactStateOnlyTopologyHelperAcceptance sha256 call)

/-- Exact parser-and-authentication behavior once the constructor has supplied
the exact hash-free plan.  This is the residual dynamic hash-loop boundary;
constructor behavior is no longer hidden inside it. -/
def Radix4BinaryCapParserAndHashLoopSourceEquality
    (sha256 : List Byte -> Digest32)
    (rustAuthenticates : StateOnlyTopologyHelperCall ->
      TopologyObservation -> Prop) : Prop :=
  ∀ call, call.queries.card = 18 ->
    (rustAuthenticates call (exactTopologyObservation call.queries) ↔
      ExactStateOnlyTopologyHelperAcceptance sha256 call)

/-- Literal composition of topology construction and the subsequent parser /
authentication loop. -/
def HelperUsingTopologyConstructor
    (rustConstructs : Finset V5Query -> Option TopologyObservation)
    (rustAuthenticates : StateOnlyTopologyHelperCall ->
      TopologyObservation -> Prop)
    (call : StateOnlyTopologyHelperCall) : Prop :=
  ∃ topology,
    rustConstructs call.queries = some topology ∧
      rustAuthenticates call topology

theorem constructor_and_hash_loop_imply_released_helper_equality
    (sha256 : List Byte -> Digest32)
    (rustConstructs : Finset V5Query -> Option TopologyObservation)
    (rustAuthenticates : StateOnlyTopologyHelperCall ->
      TopologyObservation -> Prop)
    (hconstructor : Radix4BinaryCapTopologyNewSourceEquality rustConstructs)
    (hloop : Radix4BinaryCapParserAndHashLoopSourceEquality
      sha256 rustAuthenticates) :
    VerifyStateOnlyPrivateOpeningWithTopologyReleasedSourceEquality sha256
      (HelperUsingTopologyConstructor rustConstructs rustAuthenticates) := by
  intro call hcount
  constructor
  · rintro ⟨topology, htopology, haccept⟩
    have hexact := hconstructor call.queries hcount
    have : topology = exactTopologyObservation call.queries := by
      rw [htopology] at hexact
      exact Option.some.inj hexact
    subst topology
    exact (hloop call hcount).mp haccept
  · intro hexact
    refine ⟨exactTopologyObservation call.queries,
      hconstructor call.queries hcount, ?_⟩
    exact (hloop call hcount).mpr hexact

/-- The released five-section driver needs the focused helper equality only at
its already-proved query count. -/
theorem releasedHelperSourceEquality_driver_iff_exactV5Acceptance
    (sha256 : List Byte -> Digest32)
    (rustHelperAccepts : StateOnlyTopologyHelperCall -> Prop)
    (hhelper : VerifyStateOnlyPrivateOpeningWithTopologyReleasedSourceEquality
      sha256 rustHelperAccepts)
    (call : V5ProductionCall) :
    V5DriverUsingStateOnlyHelper rustHelperAccepts call ↔
      ExactV5PrivateOpeningAcceptance sha256 call := by
  constructor
  · rintro ⟨hcount, afterC1, afterC2, afterLine1, afterLine2,
      hc1, hc2, hline1, hline2, hline3⟩
    obtain ⟨c1, hc1bytes⟩ := (hhelper _ hcount).mp hc1
    obtain ⟨c2, hc2bytes⟩ := (hhelper _ hcount).mp hc2
    obtain ⟨line1, hline1bytes⟩ := (hhelper _ hcount).mp hline1
    obtain ⟨line2, hline2bytes⟩ := (hhelper _ hcount).mp hline2
    obtain ⟨line3, hline3bytes⟩ := (hhelper _ hcount).mp hline3
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
    · apply (hhelper _ run.query_count).mpr
      refine ⟨run.sections .c1, ?_⟩
      change call.proofBytes = (run.sections .c1).wire ++ afterC1
      rw [← hrun, run.proof_eq]
      simp only [afterC1, afterC2, afterLine1, afterLine2,
        List.append_assoc]
    · apply (hhelper _ run.query_count).mpr
      exact ⟨run.sections .c2, rfl⟩
    · apply (hhelper _ run.query_count).mpr
      exact ⟨run.sections .line1, rfl⟩
    · apply (hhelper _ run.query_count).mpr
      exact ⟨run.sections .line2, rfl⟩
    · apply (hhelper _ run.query_count).mpr
      refine ⟨run.sections .line3, ?_⟩
      simp [stateOnlyCall, afterLine2]

/-- Source-shaped driver with one topology construction followed by five calls
which all receive that same topology. -/
def V5DriverUsingConstructedTopology
    (rustConstructs : Finset V5Query -> Option TopologyObservation)
    (rustAuthenticates : StateOnlyTopologyHelperCall ->
      TopologyObservation -> Prop)
    (call : V5ProductionCall) : Prop :=
  ∃ topology,
    rustConstructs call.queries = some topology ∧
      V5DriverUsingStateOnlyHelper
        (fun helperCall => rustAuthenticates helperCall topology) call

theorem constructedTopology_driver_iff_exactV5Acceptance
    (sha256 : List Byte -> Digest32)
    (rustConstructs : Finset V5Query -> Option TopologyObservation)
    (rustAuthenticates : StateOnlyTopologyHelperCall ->
      TopologyObservation -> Prop)
    (hconstructor : Radix4BinaryCapTopologyNewSourceEquality rustConstructs)
    (hloop : Radix4BinaryCapParserAndHashLoopSourceEquality
      sha256 rustAuthenticates)
    (call : V5ProductionCall) :
    V5DriverUsingConstructedTopology rustConstructs rustAuthenticates call ↔
      ExactV5PrivateOpeningAcceptance sha256 call := by
  let exactHelper : StateOnlyTopologyHelperCall -> Prop :=
    fun helperCall =>
      rustAuthenticates helperCall
        (exactTopologyObservation helperCall.queries)
  have hhelper :
      VerifyStateOnlyPrivateOpeningWithTopologyReleasedSourceEquality
        sha256 exactHelper := by
    intro helperCall hcount
    exact hloop helperCall hcount
  have hdriver :=
    releasedHelperSourceEquality_driver_iff_exactV5Acceptance
      sha256 exactHelper hhelper call
  constructor
  · rintro ⟨topology, htopology, hcalls⟩
    have hcount : call.queries.card = 18 := hcalls.1
    have hexact := hconstructor call.queries hcount
    have htopologyExact :
        topology = exactTopologyObservation call.queries := by
      rw [htopology] at hexact
      exact Option.some.inj hexact
    subst topology
    exact hdriver.mp hcalls
  · intro hexact
    have hcalls := hdriver.mpr hexact
    refine ⟨exactTopologyObservation call.queries,
      hconstructor call.queries hcalls.1, ?_⟩
    exact hcalls

/-! ## Audit -/

#print axioms activeIndices_succ
#print axioms parent_mem_next_iff_presentSlot_nonempty
#print axioms every_shared_group_is_nonempty
#print axioms slotMask_lt_sixteen
#print axioms released_section_indices_are_exact_shared_suffixes
#print axioms released_section_depths_are_shared_suffix_depths
#print axioms flattened_level_slice_is_exact
#print axioms flattened_group_slice_is_exact
#print axioms constructor_and_hash_loop_imply_released_helper_equality
#print axioms releasedHelperSourceEquality_driver_iff_exactV5Acceptance
#print axioms constructedTopology_driver_iff_exactV5Acceptance

end AspisV5TopologyConstruction
