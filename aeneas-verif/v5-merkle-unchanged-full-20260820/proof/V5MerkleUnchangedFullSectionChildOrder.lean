import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullMaskCounts
import V5MerkleUnchangedFullSectionTopologyAlignment

/-! Maintained child order for each exact released radix level. -/

namespace AspisV5MerkleUnchangedFullSectionChildOrder

open V5MerkleUnchangedCompat
variable [HashContext]

open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullMaskCounts

def localChildSlots (tree : V5PrivateSection)
    (queries : Finset V5Query) (level parent : Nat) : Finset (Fin 4) :=
  Finset.univ.filter fun slot =>
    4 * parent + slot.val ∈ activeIndices tree queries level

/-- Active children of one parent, in the exact slot order `0,1,2,3`. -/
def presentChildIndices (tree : V5PrivateSection)
    (queries : Finset V5Query) (level parent : Nat) : List Nat :=
  (List.range 4).filter (fun slot =>
      4 * parent + slot ∈ activeIndices tree queries level) |>.map
    fun slot => 4 * parent + slot

/-- Absent children of one parent, in the exact frontier slot order. -/
def absentChildIndices (tree : V5PrivateSection)
    (queries : Finset V5Query) (level parent : Nat) : List Nat :=
  (List.range 4).filter (fun slot =>
      4 * parent + slot ∉ activeIndices tree queries level) |>.map
    fun slot => 4 * parent + slot

def levelPresentChildIndices (tree : V5PrivateSection)
    (queries : Finset V5Query) (level : Nat) : List Nat :=
  (orderedActiveIndices tree queries (level + 1)).flatMap
    (presentChildIndices tree queries level)

def levelAbsentChildIndices (tree : V5PrivateSection)
    (queries : Finset V5Query) (level : Nat) : List Nat :=
  (orderedActiveIndices tree queries (level + 1)).flatMap
    (absentChildIndices tree queries level)

/-- In a filtered list, the surviving element originally at `index` occurs
after precisely the surviving prefix before `index`. -/
theorem filter_get_at_prefix
    {A : Type*} [Inhabited A] (values : List A) (keep : A → Bool)
    (index : Nat) (index_lt : index < values.length)
    (kept : keep values[index]! = true) :
    ((values.take index).filter keep).length <
        (values.filter keep).length ∧
      (values.filter keep)[((values.take index).filter keep).length]! =
        values[index]! := by
  induction values generalizing index with
  | nil => simp at index_lt
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem!_cons_zero] at kept ⊢
          simp [kept]
      | succ index =>
          have tail_lt : index < tail.length := by simpa using index_lt
          have tail_kept : keep tail[index]! = true := by
            simpa using kept
          have step := ih index tail_lt tail_kept
          by_cases head_kept : keep head = true
          · rw [List.filter_cons_of_pos head_kept,
              List.take_succ_cons, List.filter_cons_of_pos head_kept]
            simp only [List.length_cons, List.getElem!_cons_succ]
            exact ⟨by omega, step.2⟩
          · rw [List.filter_cons_of_neg head_kept,
              List.take_succ_cons, List.filter_cons_of_neg head_kept]
            exact step

theorem presentNat_localChildSlots_iff
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (level parent slot : Nat) (slot_lt : slot < 4) :
    PresentNat (localChildSlots tree queries level parent) slot ↔
      4 * parent + slot ∈ activeIndices tree queries level := by
  constructor
  · rintro ⟨bounded, bounded_eq, bounded_mem⟩
    simp only [localChildSlots, Finset.mem_filter, Finset.mem_univ,
      true_and] at bounded_mem
    simpa [bounded_eq] using bounded_mem
  · intro member
    let bounded : Fin 4 := ⟨slot, slot_lt⟩
    refine ⟨bounded, rfl, ?_⟩
    simp [localChildSlots, bounded, member]

theorem liveSlotCount_localChildSlots_eq_present_length
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (level parent : Nat) :
    liveSlotCount (localChildSlots tree queries level parent) 4 =
      (presentChildIndices tree queries level parent).length := by
  unfold liveSlotCount presentChildIndices
  rw [List.length_map]
  apply congrArg List.length
  apply List.filter_congr
  intro slot slot_mem
  have slot_lt : slot < 4 := List.mem_range.mp slot_mem
  rw [Bool.eq_iff_iff]
  simp only [presentNatBool, decide_eq_true_iff]
  exact presentNat_localChildSlots_iff tree queries level parent slot slot_lt

theorem frontierSlotCount_localChildSlots_eq_absent_length
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (level parent : Nat) :
    frontierSlotCount (localChildSlots tree queries level parent) 4 =
      (absentChildIndices tree queries level parent).length := by
  unfold frontierSlotCount absentChildIndices
  rw [List.length_map]
  apply congrArg List.length
  apply List.filter_congr
  intro slot slot_mem
  have slot_lt : slot < 4 := List.mem_range.mp slot_mem
  have presentEq : presentNatBool
      (localChildSlots tree queries level parent) slot =
      decide (4 * parent + slot ∈ activeIndices tree queries level) := by
    rw [Bool.eq_iff_iff]
    simp only [presentNatBool, decide_eq_true_iff]
    exact presentNat_localChildSlots_iff tree queries level parent slot slot_lt
  rw [decide_not]
  exact congrArg (fun value => !value) presentEq

theorem presentChildIndices_get_liveSlotCount
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (level parent slot : Nat) (slot_lt : slot < 4)
    (slot_mem : 4 * parent + slot ∈ activeIndices tree queries level) :
    (presentChildIndices tree queries level parent)[
        liveSlotCount (localChildSlots tree queries level parent) slot]! =
      4 * parent + slot := by
  let keep : Nat → Bool := fun candidate =>
    decide (4 * parent + candidate ∈ activeIndices tree queries level)
  have kept : keep (List.range 4)[slot]! = true := by
    rw [getElem!_pos (List.range 4) slot (by simpa using slot_lt),
      List.getElem_range]
    exact decide_eq_true slot_mem
  have selected := filter_get_at_prefix (List.range 4) keep slot
    (by simp [slot_lt]) kept
  have prefixFilter : (List.range slot).filter keep =
      (List.range slot).filter (presentNatBool
        (localChildSlots tree queries level parent)) := by
    apply List.filter_congr
    intro candidate candidate_mem
    have candidate_lt_slot : candidate < slot := List.mem_range.mp candidate_mem
    have candidate_lt : candidate < 4 := by omega
    rw [Bool.eq_iff_iff]
    simp only [keep, presentNatBool, decide_eq_true_iff]
    exact (presentNat_localChildSlots_iff tree queries level parent candidate
      candidate_lt).symm
  have selectedBound : ((List.range slot).filter keep).length <
      ((List.range 4).filter keep).length := by
    simpa [List.take_range, Nat.min_eq_left (Nat.le_of_lt slot_lt)] using
      selected.1
  have selectedValue :
      ((List.range 4).filter keep)[((List.range slot).filter keep).length]! =
        slot := by
    have value := selected.2
    rw [getElem!_pos (List.range 4) slot (by simpa using slot_lt),
      List.getElem_range] at value
    simpa [List.take_range, Nat.min_eq_left (Nat.le_of_lt slot_lt)] using value
  have mapBound : ((List.range slot).filter keep).length <
      (List.map (fun value => 4 * parent + value)
        ((List.range 4).filter keep)).length := by
    simpa using selectedBound
  have mapSelected :
      (List.map (fun value => 4 * parent + value)
          ((List.range 4).filter keep))[
            ((List.range slot).filter keep).length]! = 4 * parent + slot := by
    rw [getElem!_pos
      (List.map (fun value => 4 * parent + value)
        ((List.range 4).filter keep))
      ((List.range slot).filter keep).length mapBound, List.getElem_map]
    rw [← getElem!_pos ((List.range 4).filter keep)
      ((List.range slot).filter keep).length selectedBound, selectedValue]
  unfold presentChildIndices liveSlotCount
  rw [← prefixFilter]
  simpa [keep] using mapSelected

theorem liveSlotCount_lt_presentChildIndices_length
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (level parent slot : Nat) (slot_lt : slot < 4)
    (slot_mem : 4 * parent + slot ∈ activeIndices tree queries level) :
    liveSlotCount (localChildSlots tree queries level parent) slot <
      (presentChildIndices tree queries level parent).length := by
  let keep : Nat → Bool := fun candidate =>
    decide (4 * parent + candidate ∈ activeIndices tree queries level)
  have kept : keep (List.range 4)[slot]! = true := by
    rw [getElem!_pos (List.range 4) slot (by simpa using slot_lt),
      List.getElem_range]
    exact decide_eq_true slot_mem
  have selected := filter_get_at_prefix (List.range 4) keep slot
    (by simp [slot_lt]) kept
  have prefixFilter : (List.range slot).filter keep =
      (List.range slot).filter (presentNatBool
        (localChildSlots tree queries level parent)) := by
    apply List.filter_congr
    intro candidate candidate_mem
    have candidate_lt_slot : candidate < slot := List.mem_range.mp candidate_mem
    have candidate_lt : candidate < 4 := by omega
    rw [Bool.eq_iff_iff]
    simp only [keep, presentNatBool, decide_eq_true_iff]
    exact (presentNat_localChildSlots_iff tree queries level parent candidate
      candidate_lt).symm
  unfold liveSlotCount presentChildIndices
  rw [List.length_map, ← prefixFilter]
  simpa [List.take_range, Nat.min_eq_left (Nat.le_of_lt slot_lt)] using
    selected.1

theorem absentChildIndices_get_frontierSlotCount
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (level parent slot : Nat) (slot_lt : slot < 4)
    (slot_absent : 4 * parent + slot ∉ activeIndices tree queries level) :
    (absentChildIndices tree queries level parent)[
        frontierSlotCount (localChildSlots tree queries level parent) slot]! =
      4 * parent + slot := by
  let keep : Nat → Bool := fun candidate =>
    decide (4 * parent + candidate ∉ activeIndices tree queries level)
  have kept : keep (List.range 4)[slot]! = true := by
    rw [getElem!_pos (List.range 4) slot (by simpa using slot_lt),
      List.getElem_range]
    exact decide_eq_true slot_absent
  have selected := filter_get_at_prefix (List.range 4) keep slot
    (by simp [slot_lt]) kept
  have prefixFilter : (List.range slot).filter keep =
      (List.range slot).filter (fun candidate =>
        !presentNatBool (localChildSlots tree queries level parent) candidate) := by
    apply List.filter_congr
    intro candidate candidate_mem
    have candidate_lt_slot : candidate < slot := List.mem_range.mp candidate_mem
    have candidate_lt : candidate < 4 := by omega
    have presentEq : presentNatBool
        (localChildSlots tree queries level parent) candidate =
        decide (4 * parent + candidate ∈ activeIndices tree queries level) := by
      rw [Bool.eq_iff_iff]
      simp only [presentNatBool, decide_eq_true_iff]
      exact presentNat_localChildSlots_iff tree queries level parent candidate
        candidate_lt
    change decide (¬ 4 * parent + candidate ∈
      activeIndices tree queries level) =
        !presentNatBool (localChildSlots tree queries level parent) candidate
    rw [decide_not]
    exact (congrArg (fun value => !value) presentEq).symm
  have selectedBound : ((List.range slot).filter keep).length <
      ((List.range 4).filter keep).length := by
    simpa [List.take_range, Nat.min_eq_left (Nat.le_of_lt slot_lt)] using
      selected.1
  have selectedValue :
      ((List.range 4).filter keep)[((List.range slot).filter keep).length]! =
        slot := by
    have value := selected.2
    rw [getElem!_pos (List.range 4) slot (by simpa using slot_lt),
      List.getElem_range] at value
    simpa [List.take_range, Nat.min_eq_left (Nat.le_of_lt slot_lt)] using value
  have mapBound : ((List.range slot).filter keep).length <
      (List.map (fun value => 4 * parent + value)
        ((List.range 4).filter keep)).length := by
    simpa using selectedBound
  have mapSelected :
      (List.map (fun value => 4 * parent + value)
          ((List.range 4).filter keep))[
            ((List.range slot).filter keep).length]! = 4 * parent + slot := by
    rw [getElem!_pos
      (List.map (fun value => 4 * parent + value)
        ((List.range 4).filter keep))
      ((List.range slot).filter keep).length mapBound, List.getElem_map]
    rw [← getElem!_pos ((List.range 4).filter keep)
      ((List.range slot).filter keep).length selectedBound, selectedValue]
  unfold absentChildIndices frontierSlotCount
  rw [← prefixFilter]
  simpa [keep] using mapSelected

theorem frontierSlotCount_lt_absentChildIndices_length
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (level parent slot : Nat) (slot_lt : slot < 4)
    (slot_absent : 4 * parent + slot ∉ activeIndices tree queries level) :
    frontierSlotCount (localChildSlots tree queries level parent) slot <
      (absentChildIndices tree queries level parent).length := by
  let keep : Nat → Bool := fun candidate =>
    decide (4 * parent + candidate ∉ activeIndices tree queries level)
  have kept : keep (List.range 4)[slot]! = true := by
    rw [getElem!_pos (List.range 4) slot (by simpa using slot_lt),
      List.getElem_range]
    exact decide_eq_true slot_absent
  have selected := filter_get_at_prefix (List.range 4) keep slot
    (by simp [slot_lt]) kept
  have prefixFilter : (List.range slot).filter keep =
      (List.range slot).filter (fun candidate =>
        !presentNatBool
          (localChildSlots tree queries level parent) candidate) := by
    apply List.filter_congr
    intro candidate candidate_mem
    have candidate_lt_slot : candidate < slot := List.mem_range.mp candidate_mem
    have candidate_lt : candidate < 4 := by omega
    have presentEq : presentNatBool
        (localChildSlots tree queries level parent) candidate =
        decide (4 * parent + candidate ∈ activeIndices tree queries level) := by
      rw [Bool.eq_iff_iff]
      simp only [presentNatBool, decide_eq_true_iff]
      exact presentNat_localChildSlots_iff tree queries level parent candidate
        candidate_lt
    change decide (4 * parent + candidate ∉
      activeIndices tree queries level) =
        !presentNatBool (localChildSlots tree queries level parent) candidate
    rw [decide_not]
    exact (congrArg (fun value => !value) presentEq).symm
  unfold frontierSlotCount absentChildIndices
  rw [List.length_map, ← prefixFilter]
  simpa [keep, List.take_range,
    Nat.min_eq_left (Nat.le_of_lt slot_lt)] using
    selected.1

/-- Exact lookup inside a variable-width flattened list. -/
theorem flatten_get_at_group
    {A : Type*} (groups : List (List A))
    (groupOrdinal : Nat)
    (group_lt : groupOrdinal < groups.length)
    (localOrdinal : Nat)
    (local_lt : localOrdinal <
      (groups.get ⟨groupOrdinal, group_lt⟩).length) :
    (groups.flatten)[
        ((groups.map List.length).take groupOrdinal).sum + localOrdinal]? =
      some ((groups.get ⟨groupOrdinal, group_lt⟩).get
        ⟨localOrdinal, local_lt⟩) := by
  let flatOffset : Nat := ((groups.map List.length).take groupOrdinal).sum
  have dropped : groups.flatten.drop flatOffset =
      (groups.get ⟨groupOrdinal, group_lt⟩) ++
        (groups.drop (groupOrdinal + 1)).flatten := by
    dsimp [flatOffset]
    rw [List.drop_sum_flatten, List.drop_eq_getElem_cons group_lt]
    rfl
  have local_drop_lt :
      localOrdinal < (groups.flatten.drop flatOffset).length := by
    rw [dropped, List.length_append]
    omega
  have global_lt : flatOffset + localOrdinal < groups.flatten.length := by
    rw [List.length_drop] at local_drop_lt
    omega
  have local_append_lt : localOrdinal <
      ((groups.get ⟨groupOrdinal, group_lt⟩) ++
        (groups.drop (groupOrdinal + 1)).flatten).length := by
    rw [← dropped]
    exact local_drop_lt
  have value_eq : (groups.flatten)[flatOffset + localOrdinal] =
      (groups.get ⟨groupOrdinal, group_lt⟩).get
        ⟨localOrdinal, local_lt⟩ := by
    calc
    (groups.flatten)[flatOffset + localOrdinal] =
        (groups.flatten.drop flatOffset)[localOrdinal] :=
      List.getElem_drop' global_lt
    _ = (((groups.get ⟨groupOrdinal, group_lt⟩) ++
          (groups.drop (groupOrdinal + 1)).flatten).get
            ⟨localOrdinal, local_append_lt⟩) :=
      List.getElem_of_eq dropped local_drop_lt
    _ = (groups.get ⟨groupOrdinal, group_lt⟩)[localOrdinal] :=
      List.getElem_append_left local_lt
  rw [List.getElem?_eq_getElem global_lt]
  exact congrArg some value_eq

/-- A present child has this exact ordinal in the grouped maintained live
level.  `levelPresentChildIndices_eq_orderedActiveIndices` below identifies
that grouped list with the complete sorted live level. -/
theorem present_child_level_rank
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat)
    (parentOrdinal parent slot : Nat)
    (parent_lt : parentOrdinal <
      (orderedActiveIndices tree queries (level + 1)).length)
    (parent_eq :
      (orderedActiveIndices tree queries (level + 1)).get
        ⟨parentOrdinal, parent_lt⟩ = parent)
    (slot_lt : slot < 4)
    (slot_mem : 4 * parent + slot ∈ activeIndices tree queries level) :
    (levelPresentChildIndices tree queries level)[
      (((orderedActiveIndices tree queries (level + 1)).map
        (fun candidate =>
          (presentChildIndices tree queries level candidate).length)).take
        parentOrdinal).sum +
      liveSlotCount (localChildSlots tree queries level parent) slot]? =
        some (4 * parent + slot) := by
  let parents := orderedActiveIndices tree queries (level + 1)
  let groups := parents.map (presentChildIndices tree queries level)
  have group_lt : parentOrdinal < groups.length := by
    simpa [groups, parents] using parent_lt
  have selectedParent : parents.get
      ⟨parentOrdinal, by simpa [parents] using parent_lt⟩ = parent := by
    simpa [parents] using parent_eq
  have group_eq : groups.get ⟨parentOrdinal, group_lt⟩ =
      presentChildIndices tree queries level parent := by
    rw [List.get_eq_getElem]
    simp only [groups, List.getElem_map]
    apply congrArg (presentChildIndices tree queries level)
    simpa only [List.get_eq_getElem] using selectedParent
  have local_lt := liveSlotCount_lt_presentChildIndices_length tree queries
    level parent slot slot_lt slot_mem
  have group_local_lt :
      liveSlotCount (localChildSlots tree queries level parent) slot <
        (groups.get ⟨parentOrdinal, group_lt⟩).length := by
    rw [group_eq]
    exact local_lt
  have flattened := flatten_get_at_group groups parentOrdinal group_lt
    (liveSlotCount (localChildSlots tree queries level parent) slot)
    group_local_lt
  have localValue := presentChildIndices_get_liveSlotCount tree queries level
    parent slot slot_lt slot_mem
  have groupValue :
      (groups.get ⟨parentOrdinal, group_lt⟩).get
          ⟨liveSlotCount (localChildSlots tree queries level parent) slot,
            group_local_lt⟩ =
        4 * parent + slot := by
    calc
      (groups.get ⟨parentOrdinal, group_lt⟩).get
          ⟨liveSlotCount (localChildSlots tree queries level parent) slot,
            group_local_lt⟩ =
          (presentChildIndices tree queries level parent).get
            ⟨liveSlotCount (localChildSlots tree queries level parent) slot,
              local_lt⟩ :=
        List.getElem_of_eq group_eq group_local_lt
      _ = 4 * parent + slot := by
        rw [List.get_eq_getElem]
        rw [← getElem!_pos (presentChildIndices tree queries level parent)
          (liveSlotCount (localChildSlots tree queries level parent) slot)
          local_lt]
        exact localValue
  have flattenedValue : groups.flatten[
      ((groups.map List.length).take parentOrdinal).sum +
        liveSlotCount (localChildSlots tree queries level parent) slot]? =
      some (4 * parent + slot) := by
    rw [flattened, groupValue]
  simpa [levelPresentChildIndices, groups, parents, List.flatMap,
    Function.comp_def] using flattenedValue

/-- An absent child has this exact ordinal within its maintained radix
frontier level. -/
theorem absent_child_level_frontier_rank
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat)
    (parentOrdinal parent slot : Nat)
    (parent_lt : parentOrdinal <
      (orderedActiveIndices tree queries (level + 1)).length)
    (parent_eq :
      (orderedActiveIndices tree queries (level + 1)).get
        ⟨parentOrdinal, parent_lt⟩ = parent)
    (slot_lt : slot < 4)
    (slot_absent : 4 * parent + slot ∉ activeIndices tree queries level) :
    (levelAbsentChildIndices tree queries level)[
      (((orderedActiveIndices tree queries (level + 1)).map
        (fun candidate =>
          (absentChildIndices tree queries level candidate).length)).take
        parentOrdinal).sum +
      frontierSlotCount (localChildSlots tree queries level parent) slot]? =
        some (4 * parent + slot) := by
  let parents := orderedActiveIndices tree queries (level + 1)
  let groups := parents.map (absentChildIndices tree queries level)
  have group_lt : parentOrdinal < groups.length := by
    simpa [groups, parents] using parent_lt
  have selectedParent : parents.get
      ⟨parentOrdinal, by simpa [parents] using parent_lt⟩ = parent := by
    simpa [parents] using parent_eq
  have group_eq : groups.get ⟨parentOrdinal, group_lt⟩ =
      absentChildIndices tree queries level parent := by
    rw [List.get_eq_getElem]
    simp only [groups, List.getElem_map]
    apply congrArg (absentChildIndices tree queries level)
    simpa only [List.get_eq_getElem] using selectedParent
  have local_lt := frontierSlotCount_lt_absentChildIndices_length tree queries
    level parent slot slot_lt slot_absent
  have group_local_lt :
      frontierSlotCount (localChildSlots tree queries level parent) slot <
        (groups.get ⟨parentOrdinal, group_lt⟩).length := by
    rw [group_eq]
    exact local_lt
  have flattened := flatten_get_at_group groups parentOrdinal group_lt
    (frontierSlotCount (localChildSlots tree queries level parent) slot)
    group_local_lt
  have localValue := absentChildIndices_get_frontierSlotCount tree queries
    level parent slot slot_lt slot_absent
  have groupValue :
      (groups.get ⟨parentOrdinal, group_lt⟩).get
          ⟨frontierSlotCount (localChildSlots tree queries level parent) slot,
            group_local_lt⟩ =
        4 * parent + slot := by
    calc
      (groups.get ⟨parentOrdinal, group_lt⟩).get
          ⟨frontierSlotCount (localChildSlots tree queries level parent) slot,
            group_local_lt⟩ =
          (absentChildIndices tree queries level parent).get
            ⟨frontierSlotCount
                (localChildSlots tree queries level parent) slot,
              local_lt⟩ :=
        List.getElem_of_eq group_eq group_local_lt
      _ = 4 * parent + slot := by
        rw [List.get_eq_getElem]
        rw [← getElem!_pos (absentChildIndices tree queries level parent)
          (frontierSlotCount (localChildSlots tree queries level parent) slot)
          local_lt]
        exact localValue
  have flattenedValue : groups.flatten[
      ((groups.map List.length).take parentOrdinal).sum +
        frontierSlotCount (localChildSlots tree queries level parent) slot]? =
      some (4 * parent + slot) := by
    rw [flattened, groupValue]
  simpa [levelAbsentChildIndices, groups, parents, List.flatMap,
    Function.comp_def] using flattenedValue

theorem mem_presentChildIndices_iff
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (level parent index : Nat) :
    index ∈ presentChildIndices tree queries level parent ↔
      index ∈ activeIndices tree queries level ∧ index / 4 = parent := by
  constructor
  · intro member
    simp only [presentChildIndices, List.mem_map, List.mem_filter,
      List.mem_range] at member
    obtain ⟨slot, ⟨slot_lt, slot_mem⟩, rfl⟩ := member
    constructor
    · exact of_decide_eq_true slot_mem
    · omega
  · rintro ⟨index_mem, parent_eq⟩
    let slot := index % 4
    have slot_lt : slot < 4 := Nat.mod_lt _ (by decide)
    have index_eq : 4 * parent + slot = index := by
      have split := Nat.mod_add_div index 4
      omega
    simp only [presentChildIndices, List.mem_map, List.mem_filter,
      List.mem_range]
    exact ⟨slot, ⟨slot_lt, by
      apply decide_eq_true
      simpa [index_eq] using index_mem⟩, index_eq⟩

theorem mem_levelPresentChildIndices_iff
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (level index : Nat) :
    index ∈ levelPresentChildIndices tree queries level ↔
      index ∈ activeIndices tree queries level := by
  constructor
  · intro member
    simp only [levelPresentChildIndices, List.mem_flatMap] at member
    obtain ⟨parent, _, child⟩ := member
    exact (mem_presentChildIndices_iff tree queries level parent index).mp child |>.1
  · intro index_mem
    have parent_mem : index / 4 ∈ activeIndices tree queries (level + 1) := by
      rw [activeIndices_succ]
      exact Finset.mem_image.mpr ⟨index, index_mem, rfl⟩
    have parent_list : index / 4 ∈
        orderedActiveIndices tree queries (level + 1) :=
      (Finset.mem_sort (fun left right : Nat => left ≤ right)).mpr parent_mem
    simp only [levelPresentChildIndices, List.mem_flatMap]
    exact ⟨index / 4, parent_list,
      (mem_presentChildIndices_iff tree queries level (index / 4) index).mpr
        ⟨index_mem, rfl⟩⟩

private theorem orderedActiveIndices_pairwise_lt
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat) :
    (orderedActiveIndices tree queries level).Pairwise (.<.) := by
  have le := orderedActiveIndices_sorted tree queries level
  have ne : (orderedActiveIndices tree queries level).Pairwise (.≠.) :=
    List.nodup_iff_pairwise_ne.mp
      (orderedActiveIndices_nodup tree queries level)
  exact (le.and ne).imp (by
    intro left right facts
    omega)

theorem levelPresentChildIndices_pairwise_lt
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat) :
    (levelPresentChildIndices tree queries level).Pairwise (.<.) := by
  rw [levelPresentChildIndices, List.pairwise_flatMap]
  constructor
  · intro parent parent_mem
    unfold presentChildIndices
    rw [List.pairwise_map]
    exact (List.pairwise_lt_range.filter _).imp (by
      intro left right less
      omega)
  · apply (orderedActiveIndices_pairwise_lt tree queries (level + 1)).imp
    intro leftParent rightParent parents_lt left left_mem right right_mem
    have left_parent :=
      (mem_presentChildIndices_iff tree queries level leftParent left).mp
        left_mem |>.2
    have right_parent :=
      (mem_presentChildIndices_iff tree queries level rightParent right).mp
        right_mem |>.2
    have left_split := Nat.mod_add_div left 4
    have right_split := Nat.mod_add_div right 4
    have left_slot := Nat.mod_lt left (by decide : 0 < 4)
    have right_slot := Nat.mod_lt right (by decide : 0 < 4)
    omega

/-- Grouping by parent and then visiting slots `0,1,2,3` reconstructs the
complete maintained live level without omission, duplication, or reordering. -/
theorem levelPresentChildIndices_eq_orderedActiveIndices
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat) :
    levelPresentChildIndices tree queries level =
      orderedActiveIndices tree queries level := by
  apply List.Subset.antisymm_of_pairwise
    (levelPresentChildIndices_pairwise_lt tree queries level)
    (orderedActiveIndices_pairwise_lt tree queries level)
  · intro index member
    exact (Finset.mem_sort (fun left right : Nat => left ≤ right)).mpr
      ((mem_levelPresentChildIndices_iff tree queries level index).mp member)
  · intro index member
    exact (mem_levelPresentChildIndices_iff tree queries level index).mpr
      ((Finset.mem_sort (fun left right : Nat => left ≤ right)).mp member)

/-- The maintained radix frontier is exactly the concatenation of the absent
child lists at every level, with the level attached to each index. -/
theorem radixFrontierPositions_eq_levelAbsentChildIndices
    (tree : V5PrivateSection) (queries : Finset V5Query) :
    radixFrontierPositions tree queries =
      (List.range (radixLevelCount tree)).flatMap fun level =>
        (levelAbsentChildIndices tree queries level).map fun index =>
          ({ level := level, index := index } : FrontierPosition) := by
  unfold radixFrontierPositions levelAbsentChildIndices absentChildIndices
  simp only [List.map_flatMap, List.map_map]
  congr 1

#print axioms mem_presentChildIndices_iff
#print axioms mem_levelPresentChildIndices_iff
#print axioms liveSlotCount_localChildSlots_eq_present_length
#print axioms frontierSlotCount_localChildSlots_eq_absent_length
#print axioms filter_get_at_prefix
#print axioms presentChildIndices_get_liveSlotCount
#print axioms liveSlotCount_lt_presentChildIndices_length
#print axioms absentChildIndices_get_frontierSlotCount
#print axioms frontierSlotCount_lt_absentChildIndices_length
#print axioms flatten_get_at_group
#print axioms present_child_level_rank
#print axioms absent_child_level_frontier_rank
#print axioms levelPresentChildIndices_pairwise_lt
#print axioms levelPresentChildIndices_eq_orderedActiveIndices
#print axioms radixFrontierPositions_eq_levelAbsentChildIndices

end AspisV5MerkleUnchangedFullSectionChildOrder
