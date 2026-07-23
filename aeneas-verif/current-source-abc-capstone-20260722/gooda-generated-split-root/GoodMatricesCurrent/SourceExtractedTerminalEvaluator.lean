import GoodMatricesCurrent.SourceExtractedTerminalFieldAll
import GoodMatricesCurrent.SourceExtractedTerminalWeights
import AspisFormal.V5GoodGateDotBatching

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedTerminalEvaluator

open GoodMatricesCurrent.SourceExtractedTerminalField
open GoodMatricesCurrent.SourceExtractedTerminalWeights
open AspisV5ComponentCQM31TowerExact
open AspisV5M31RawMulReduction
open AspisV5GoodGateDotBatching

abbrev LocalNatural := Array LocalM31 48#usize
abbrev LocalWeights := Array LocalQM31 64#usize
abbrev Raw4 := Array Std.U64 4#usize

def naturalEntry (natural : LocalNatural) (index : Fin 48) : LocalM31 :=
  natural.val[index.val]'(by rw [natural.property]; exact index.isLt)

def naturalToExact (natural : LocalNatural) : Fin 48 → ExactM31 :=
  fun index => (naturalEntry natural index).val

def CanonicalLocalNatural (natural : LocalNatural) : Prop :=
  ∀ index : Fin 48, CanonicalLocalM31 (naturalEntry natural index)

def qm31Limb (value : LocalQM31) (limb : Fin 4) : LocalM31 :=
  match limb.val with
  | 0 => value.c0.a
  | 1 => value.c0.b
  | 2 => value.c1.a
  | _ => value.c1.b

def exactQM31Limb (value : ExactQM31) (limb : Fin 4) : ExactM31 :=
  match limb.val with
  | 0 => value.re.re
  | 1 => value.re.im
  | 2 => value.im.re
  | _ => value.im.im

def rawEntry (raw : Raw4) (limb : Fin 4) : Std.U64 :=
  raw.val[limb.val]'(by rw [raw.property]; exact limb.isLt)

def naturalWord (natural : LocalNatural) (index : Nat) : Nat :=
  if hindex : index < 48 then (naturalEntry natural ⟨index, hindex⟩).val else 0

def weightWord (weights : LocalWeights) (index limb : Nat) : Nat :=
  if hindex : index < 64 then
    if hlimb : limb < 4 then
      (qm31Limb (weightEntry weights ⟨index, hindex⟩) ⟨limb, hlimb⟩).val
    else 0
  else 0

def deployedLeft (natural : LocalNatural) (shift : Fin 12) (logical : Nat) : Nat :=
  naturalWord natural (deployedSupportIndex shift logical)

def deployedWeight (weights : LocalWeights) (shift : Fin 12)
    (mask limb logical : Nat) : Nat :=
  weightWord weights (Nat.xor (deployedSupportIndex shift logical) mask) limb

def paddedLeft (natural : LocalNatural) (shift : Fin 12) : Fin 24 → Nat :=
  zeroPad24 (deployedSupportCount shift) (deployedLeft natural shift)

def paddedWeight (weights : LocalWeights) (shift : Fin 12)
    (mask limb : Nat) : Fin 24 → Nat :=
  zeroPad24 (deployedSupportCount shift)
    (deployedWeight weights shift mask limb)

def deployedBatchedLimb (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask limb : Nat) : Nat :=
  batchedDot24 (paddedLeft natural shift)
    (paddedWeight weights shift mask limb)

def deployedBatchedQM31 (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask : Nat) : ExactQM31 :=
  ⟨⟨deployedBatchedLimb natural weights shift mask 0,
      deployedBatchedLimb natural weights shift mask 1⟩,
    ⟨deployedBatchedLimb natural weights shift mask 2,
      deployedBatchedLimb natural weights shift mask 3⟩⟩

def blockRawAt (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask limb block : Nat) : Nat :=
  if hblock : block < 6 then
    blockRaw (paddedLeft natural shift) (paddedWeight weights shift mask limb)
      ⟨block, hblock⟩
  else 0

def outerPrefix (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask limb blocks : Nat) : Nat :=
  ∑ block ∈ Finset.range blocks,
    rawReduceU64 (blockRawAt natural weights shift mask limb block)

def slotPrefix (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask limb block slots : Nat) : Nat :=
  ∑ slot ∈ Finset.range slots,
    deployedLeft natural shift (4 * block + slot) *
      deployedWeight weights shift mask limb (4 * block + slot)

def MaskBound (mask : Nat) : Prop :=
  ∀ index, index < 48 → Nat.xor index mask < 64

theorem mask_zero_bound : MaskBound 0 := by
  intro index hindex
  simpa using hindex.trans_le (by norm_num : 48 ≤ 64)

theorem mask_six_bound : MaskBound 6 := by
  intro index hindex
  have hi : index < 2 ^ 6 := by norm_num at hindex ⊢; omega
  have hs : 6 < 2 ^ 6 := by norm_num
  exact Nat.bitwise_lt_two_pow hi hs

theorem supportIndex_lt_48 (shift : Fin 12) (logical : Nat)
    (hlogical : logical < deployedSupportCount shift) :
    deployedSupportIndex shift logical < 48 := by
  have hend := deployedSupportIndex_lt_end shift logical hlogical
  have hshift := shift.isLt
  unfold deployedSupportEnd at hend
  omega

theorem support_runtime_shape (shift : Fin 12) :
    shift.val % 2 + 2 * deployedSupportCount shift =
      deployedSupportEnd shift + 1 := by
  have hshift := shift.isLt
  unfold deployedSupportCount deployedSupportEnd
  omega

theorem naturalWord_active (natural : LocalNatural) (index : Nat)
    (hindex : index < 48) :
    naturalWord natural index = (naturalEntry natural ⟨index, hindex⟩).val := by
  simp [naturalWord, hindex]

theorem weightWord_active (weights : LocalWeights) (index limb : Nat)
    (hindex : index < 64) (hlimb : limb < 4) :
    weightWord weights index limb =
      (qm31Limb (weightEntry weights ⟨index, hindex⟩) ⟨limb, hlimb⟩).val := by
  simp [weightWord, hindex, hlimb]

theorem deployedLeft_canonical (natural : LocalNatural)
    (hnatural : CanonicalLocalNatural natural) (shift : Fin 12)
    (logical : Nat) (hlogical : logical < deployedSupportCount shift) :
    deployedLeft natural shift logical < P := by
  rw [deployedLeft, naturalWord_active _ _
    (supportIndex_lt_48 shift logical hlogical)]
  exact hnatural _

theorem deployedWeight_canonical (weights : LocalWeights)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (mask limb logical : Nat) (hmask : MaskBound mask) (hlimb : limb < 4)
    (hlogical : logical < deployedSupportCount shift) :
    deployedWeight weights shift mask limb logical < P := by
  have hindex48 := supportIndex_lt_48 shift logical hlogical
  have hindex64 := hmask _ hindex48
  rw [deployedWeight, weightWord_active _ _ _ hindex64 hlimb]
  have hcanonical := hweights ⟨Nat.xor (deployedSupportIndex shift logical) mask,
    hindex64⟩
  rcases hcanonical with ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩
  have hcases : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
  rcases hcases with h | h | h | h <;> subst limb <;>
    simp [qm31Limb] <;> assumption

theorem paddedLeft_canonical (natural : LocalNatural)
    (hnatural : CanonicalLocalNatural natural) (shift : Fin 12) :
    ∀ index, paddedLeft natural shift index < P := by
  apply zeroPad24_canonical
  intro logical hlogical
  exact deployedLeft_canonical natural hnatural shift logical hlogical

theorem paddedWeight_canonical (weights : LocalWeights)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (mask limb : Nat) (hmask : MaskBound mask) (hlimb : limb < 4) :
    ∀ index, paddedWeight weights shift mask limb index < P := by
  apply zeroPad24_canonical
  intro logical hlogical
  exact deployedWeight_canonical weights hweights shift mask limb logical
    hmask hlimb hlogical

theorem slotPrefix_succ (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask limb block slots : Nat) :
    slotPrefix natural weights shift mask limb block (slots + 1) =
      slotPrefix natural weights shift mask limb block slots +
        deployedLeft natural shift (4 * block + slots) *
          deployedWeight weights shift mask limb (4 * block + slots) := by
  unfold slotPrefix
  rw [Finset.sum_range_succ]

theorem outerPrefix_succ (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask limb blocks : Nat) :
    outerPrefix natural weights shift mask limb (blocks + 1) =
      outerPrefix natural weights shift mask limb blocks +
        rawReduceU64 (blockRawAt natural weights shift mask limb blocks) := by
  unfold outerPrefix
  rw [Finset.sum_range_succ]

theorem blockRawAt_eq_sum_range_four (natural : LocalNatural)
    (weights : LocalWeights) (shift : Fin 12) (mask limb block : Nat)
    (hblock : block < 6) :
    blockRawAt natural weights shift mask limb block =
      ∑ slot ∈ Finset.range 4,
        if 4 * block + slot < deployedSupportCount shift then
          deployedLeft natural shift (4 * block + slot) *
            deployedWeight weights shift mask limb (4 * block + slot)
        else 0 := by
  unfold blockRawAt
  rw [dif_pos hblock]
  unfold blockRaw paddedLeft paddedWeight
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro slot hslot
  have hslot4 := Finset.mem_range.mp hslot
  by_cases hactive : 4 * block + slot < deployedSupportCount shift
  · simp [blockIndex, zeroPad24, hslot4, hactive]
  · simp [blockIndex, zeroPad24, hslot4, hactive]

theorem slotPrefix_eq_blockRawAt (natural : LocalNatural)
    (weights : LocalWeights) (shift : Fin 12) (mask limb block slots : Nat)
    (hblock : block < 6) (hslots : slots ≤ 4)
    (hprocessed : 4 * block + slots ≤ deployedSupportCount shift)
    (hfinal : slots = 4 ∨
      deployedSupportCount shift ≤ 4 * block + slots) :
    slotPrefix natural weights shift mask limb block slots =
      blockRawAt natural weights shift mask limb block := by
  rw [blockRawAt_eq_sum_range_four natural weights shift mask limb block hblock]
  unfold slotPrefix
  calc
    (∑ slot ∈ Finset.range slots,
        deployedLeft natural shift (4 * block + slot) *
          deployedWeight weights shift mask limb (4 * block + slot)) =
        ∑ slot ∈ Finset.range slots,
          if 4 * block + slot < deployedSupportCount shift then
            deployedLeft natural shift (4 * block + slot) *
              deployedWeight weights shift mask limb (4 * block + slot)
          else 0 := by
      apply Finset.sum_congr rfl
      intro slot hslot
      rw [if_pos]
      have hslot' := Finset.mem_range.mp hslot
      omega
    _ = ∑ slot ∈ Finset.range 4,
          if 4 * block + slot < deployedSupportCount shift then
            deployedLeft natural shift (4 * block + slot) *
              deployedWeight weights shift mask limb (4 * block + slot)
          else 0 := by
      apply Finset.sum_subset
      · intro slot hslot
        simp only [Finset.mem_range] at hslot ⊢
        omega
      · intro slot hslot4 hslot
        have hslot4' := Finset.mem_range.mp hslot4
        have hnslot : slots ≤ slot := by simpa using hslot
        rw [if_neg]
        rcases hfinal with hfull | hterminal
        · omega
        · omega

theorem slotPrefix_lt_u64 (natural : LocalNatural) (weights : LocalWeights)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (mask limb block slots : Nat) (hmask : MaskBound mask)
    (hlimb : limb < 4) (hslots : slots ≤ 4)
    (hprocessed : 4 * block + slots ≤ deployedSupportCount shift) :
    slotPrefix natural weights shift mask limb block slots < 2 ^ 64 := by
  have hterm : ∀ slot ∈ Finset.range slots,
      deployedLeft natural shift (4 * block + slot) *
          deployedWeight weights shift mask limb (4 * block + slot) ≤
        (P - 1) ^ 2 := by
    intro slot hslot
    have hslot' := Finset.mem_range.mp hslot
    have hlogical : 4 * block + slot < deployedSupportCount shift := by omega
    have hl := deployedLeft_canonical natural hnatural shift _ hlogical
    have hw := deployedWeight_canonical weights hweights shift mask limb _
      hmask hlimb hlogical
    have hl' : deployedLeft natural shift (4 * block + slot) ≤ P - 1 :=
      Nat.le_pred_of_lt hl
    have hw' : deployedWeight weights shift mask limb
        (4 * block + slot) ≤ P - 1 := Nat.le_pred_of_lt hw
    simpa [pow_two] using Nat.mul_le_mul hl' hw'
  calc
    slotPrefix natural weights shift mask limb block slots ≤
        ∑ _slot ∈ Finset.range slots, (P - 1) ^ 2 := by
      unfold slotPrefix
      exact Finset.sum_le_sum fun slot hslot => hterm slot hslot
    _ = slots * (P - 1) ^ 2 := by simp
    _ ≤ 4 * (P - 1) ^ 2 := Nat.mul_le_mul_right _ hslots
    _ < 2 ^ 64 := four_max_products_lt_u64

theorem natural_index_call (natural : LocalNatural) (index : Std.Usize)
    (hindex : index.val < 48) :
    Array.index_usize natural index =
      .ok (naturalEntry natural ⟨index.val, hindex⟩) := by
  exact Array.index_usize_eq_ok_of_getElem_eq natural index
    (by rw [natural.property]; exact hindex) _ rfl

theorem raw_index_call (raw : Raw4) (limb : Std.Usize)
    (hlimb : limb.val < 4) :
    Array.index_usize raw limb = .ok (rawEntry raw ⟨limb.val, hlimb⟩) := by
  exact Array.index_usize_eq_ok_of_getElem_eq raw limb
    (by rw [raw.property]; exact hlimb) _ rfl

theorem raw_index_zero_call (raw : Raw4) :
    Array.index_usize raw 0#usize = .ok (rawEntry raw (0 : Fin 4)) := by
  have hcall := raw_index_call raw 0#usize (by norm_num)
  rw [hcall]
  congr 2

theorem raw_index_one_call (raw : Raw4) :
    Array.index_usize raw 1#usize = .ok (rawEntry raw (1 : Fin 4)) := by
  have hcall := raw_index_call raw 1#usize (by norm_num)
  rw [hcall]
  congr 2

theorem raw_index_two_call (raw : Raw4) :
    Array.index_usize raw 2#usize = .ok (rawEntry raw (2 : Fin 4)) := by
  have hcall := raw_index_call raw 2#usize (by norm_num)
  rw [hcall]
  congr 2

theorem raw_index_three_call (raw : Raw4) :
    Array.index_usize raw 3#usize = .ok (rawEntry raw (3 : Fin 4)) := by
  have hcall := raw_index_call raw 3#usize (by norm_num)
  rw [hcall]
  congr 2

theorem raw_update_call (raw : Raw4) (limb : Std.Usize)
    (hlimb : limb.val < 4) (value : Std.U64) :
    Array.update raw limb value = .ok (raw.set limb value) := by
  exact Array.update_eq_ok _ _ _ (by rw [raw.property]; exact hlimb)

@[simp] theorem rawEntry_set_same (raw : Raw4) (limb : Std.Usize)
    (hlimb : limb.val < 4) (value : Std.U64) :
    rawEntry (raw.set limb value) ⟨limb.val, hlimb⟩ = value := by
  unfold rawEntry
  exact List.getElem_set_self (by
    simp only [List.length_set]
    rw [raw.property]
    exact hlimb)

@[simp] theorem rawEntry_set_other (raw : Raw4) (limb : Std.Usize)
    (value : Std.U64) (output : Fin 4) (hne : limb.val ≠ output.val) :
    rawEntry (raw.set limb value) output = rawEntry raw output := by
  unfold rawEntry
  exact List.getElem_set_ne hne (by
    simp only [List.length_set]
    rw [raw.property]
    exact output.isLt)

theorem rawEntry_set_zero (raw : Raw4) (value : Std.U64) :
    rawEntry (raw.set 0#usize value) (0 : Fin 4) = value := by
  unfold rawEntry
  exact List.getElem_set_self (by
    simp only [List.length_set]
    rw [raw.property]
    norm_num)

theorem rawEntry_set_one (raw : Raw4) (value : Std.U64) :
    rawEntry (raw.set 1#usize value) (1 : Fin 4) = value := by
  unfold rawEntry
  exact List.getElem_set_self (by
    simp only [List.length_set]
    rw [raw.property]
    norm_num)

theorem rawEntry_set_two (raw : Raw4) (value : Std.U64) :
    rawEntry (raw.set 2#usize value) (2 : Fin 4) = value := by
  unfold rawEntry
  exact List.getElem_set_self (by
    simp only [List.length_set]
    rw [raw.property]
    norm_num)

theorem rawEntry_set_three (raw : Raw4) (value : Std.U64) :
    rawEntry (raw.set 3#usize value) (3 : Fin 4) = value := by
  unfold rawEntry
  exact List.getElem_set_self (by
    simp only [List.length_set]
    rw [raw.property]
    norm_num)

theorem usize_xor_val (left right : Std.Usize) :
    (left ^^^ right).val = Nat.xor left.val right.val := by
  rfl

theorem usize_wrapping_add_two_val (value : Std.Usize)
    (hvalue : value.val + 2 < Std.Usize.size) :
    (Std.Usize.wrapping_add value 2#usize).val = value.val + 2 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa using hvalue

theorem usize_wrapping_add_eight_val (value : Std.Usize)
    (hvalue : value.val + 8 < Std.Usize.size) :
    (Std.Usize.wrapping_add value 8#usize).val = value.val + 8 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa using hvalue

theorem usize_wrapping_add_one_val (value : Std.Usize)
    (hvalue : value.val + 1 < Std.Usize.size) :
    (Std.Usize.wrapping_add value 1#usize).val = value.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa using hvalue

theorem u64_wrapping_mul_exact (left right : Std.U64)
    (hbound : left.val * right.val < 2 ^ 64) :
    (Std.U64.wrapping_mul left right).val = left.val * right.val := by
  rw [Std.U64.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [UScalar.size, Std.U64.size, Std.U64.numBits] using hbound

theorem u64_wrapping_add_exact (left right : Std.U64)
    (hbound : left.val + right.val < 2 ^ 64) :
    (Std.U64.wrapping_add left right).val = left.val + right.val := by
  rw [Std.U64.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [UScalar.size, Std.U64.size, Std.U64.numBits] using hbound

theorem usize_min_spec (left right : Std.Usize) :
    ∃ result : Std.Usize,
      core.cmp.min core.cmp.OrdUsize left right = .ok result ∧
      result.val = Nat.min left.val right.val := by
  by_cases hlt : left.val < right.val
  · refine ⟨left, ?_, by simp [Nat.min_eq_left (Nat.le_of_lt hlt)]⟩
    simp [core.cmp.min,
      core.cmp.impls.OrdUsize.min,
      (UScalar.lt_equiv left right).2 hlt]
  · have hle : right.val ≤ left.val := by omega
    refine ⟨right, ?_, by simp [Nat.min_eq_right hle]⟩
    have hnlt : ¬ left < right := by
      intro h
      exact hlt ((UScalar.lt_equiv _ _).1 h)
    simp [core.cmp.min,
      core.cmp.impls.OrdUsize.min, hnlt]

private abbrev singleInnerBody :=
  v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0_loop0.body

private abbrev singleInnerLoop :=
  v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0_loop0

def SingleInnerInvariant (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask block slots : Nat) (blockEnd index : Std.Usize)
    (raw : Raw4) : Prop :=
  block < 6 ∧
  4 * block < deployedSupportCount shift ∧
  slots ≤ 4 ∧
  4 * block + slots ≤ deployedSupportCount shift ∧
  index.val = shift.val % 2 + 2 * (4 * block + slots) ∧
  blockEnd.val = Nat.min
    (shift.val % 2 + 2 * (4 * block) + 8) (deployedSupportEnd shift) ∧
  ∀ limb : Fin 4,
    (rawEntry raw limb).val =
      slotPrefix natural weights shift mask limb.val block slots

private theorem source_index_lt_blockEnd_iff (natural : LocalNatural)
    (weights : LocalWeights) (shift : Fin 12) (mask block slots : Nat)
    (blockEnd index : Std.Usize) (raw : Raw4)
    (hinvariant : SingleInnerInvariant natural weights shift mask block slots
      blockEnd index raw) :
    index.val < blockEnd.val ↔
      slots < 4 ∧ 4 * block + slots < deployedSupportCount shift := by
  rcases hinvariant with ⟨hblock, hblockActive, hslots, hprocessed,
    hindex, hblockEnd, _⟩
  rw [hindex, hblockEnd]
  have hshape := support_runtime_shape shift
  constructor <;> intro h
  · have hleft := lt_of_lt_of_le h (Nat.min_le_left _ _)
    have hright := lt_of_lt_of_le h (Nat.min_le_right _ _)
    constructor <;> omega
  · apply lt_min
    · omega
    · omega

private theorem usize_size_large : 128 < Std.Usize.size := by
  rcases System.Platform.numBits_eq with hp | hp <;>
    norm_num [Std.Usize.size, Std.Usize.numBits, hp]

private theorem singleInnerBody_step (natural : LocalNatural)
    (weights : LocalWeights) (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (runtimeMask : Std.Usize) (mask block slots : Nat)
    (blockEnd index : Std.Usize) (raw : Raw4)
    (hruntimeMask : runtimeMask.val = mask) (hmask : MaskBound mask)
    (hinvariant : SingleInnerInvariant natural weights shift mask block slots
      blockEnd index raw)
    (hcontinue : slots < 4 ∧
      4 * block + slots < deployedSupportCount shift) :
    ∃ state : Std.Usize × Raw4,
      singleInnerBody natural weights runtimeMask blockEnd index raw =
        .ok (.cont state) ∧
      SingleInnerInvariant natural weights shift mask block (slots + 1)
        blockEnd state.1 state.2 := by
  rcases hinvariant with ⟨hblock, hblockActive, hslots, hprocessed,
    hindex, hblockEnd, hraw⟩
  have hlogical : 4 * block + slots < deployedSupportCount shift := hcontinue.2
  have hphysical48 := supportIndex_lt_48 shift (4 * block + slots) hlogical
  have hphysicalEq : deployedSupportIndex shift (4 * block + slots) =
      index.val := by
    unfold deployedSupportIndex
    rw [hindex]
  have hindex48 : index.val < 48 := by simpa [hphysicalEq] using hphysical48
  have hxor64 : Nat.xor index.val mask < 64 := hmask _ hindex48
  let xorIndex := index ^^^ runtimeMask
  have hxorIndex : xorIndex.val = Nat.xor index.val mask := by
    unfold xorIndex
    rw [usize_xor_val, hruntimeMask]
  have hxorIndex64 : xorIndex.val < 64 := by rw [hxorIndex]; exact hxor64
  let weight := weightEntry weights ⟨xorIndex.val, hxorIndex64⟩
  have hweightCall : Array.index_usize weights xorIndex = .ok weight := by
    exact weight_index_call weights xorIndex hxorIndex64
  have hweightEq : weight = weightEntry weights
      ⟨Nat.xor (deployedSupportIndex shift (4 * block + slots)) mask,
        by rw [hphysicalEq]; exact hxor64⟩ := by
    unfold weight
    apply congrArg (weightEntry weights)
    apply Fin.ext
    calc
      xorIndex.val = Nat.xor index.val mask := hxorIndex
      _ = Nat.xor (deployedSupportIndex shift (4 * block + slots)) mask :=
        congrArg (fun value => Nat.xor value mask) hphysicalEq.symm
  let m := naturalEntry natural ⟨index.val, hindex48⟩
  have hmCall : Array.index_usize natural index = .ok m := by
    exact natural_index_call natural index hindex48
  have hmEq : m = naturalEntry natural
      ⟨deployedSupportIndex shift (4 * block + slots), hphysical48⟩ := by
    unfold m
    congr 1
    apply Fin.ext
    exact hphysicalEq.symm
  let value : Std.U64 := core.convert.num.FromU64U32.from m
  have hvalue : value.val = m.val := by simp [value]
  have hmWord : m.val = deployedLeft natural shift (4 * block + slots) := by
    rw [deployedLeft, naturalWord_active _ _ hphysical48, hmEq]
  have hweightWord (limb : Fin 4) :
      (qm31Limb weight limb).val =
        deployedWeight weights shift mask limb.val (4 * block + slots) := by
    have hsxor64 : Nat.xor
        (deployedSupportIndex shift (4 * block + slots)) mask < 64 := by
      rw [hphysicalEq]
      exact hxor64
    rw [deployedWeight,
      weightWord_active weights _ limb.val hsxor64 limb.isLt, hweightEq]
  have hleftCanonical := deployedLeft_canonical natural hnatural shift
    (4 * block + slots) hlogical
  have hweightCanonical (limb : Fin 4) :=
    deployedWeight_canonical weights hweights shift mask limb.val
      (4 * block + slots) hmask limb.isLt hlogical
  have hproductBound (limb : Fin 4) :
      m.val * (qm31Limb weight limb).val < 2 ^ 64 := by
    rw [hmWord, hweightWord]
    have hl' : deployedLeft natural shift (4 * block + slots) ≤ P - 1 :=
      Nat.le_pred_of_lt hleftCanonical
    have hw' : deployedWeight weights shift mask limb.val
        (4 * block + slots) ≤ P - 1 :=
      Nat.le_pred_of_lt (hweightCanonical limb)
    calc
      deployedLeft natural shift (4 * block + slots) *
          deployedWeight weights shift mask limb.val (4 * block + slots) ≤
        (P - 1) ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul hl' hw'
      _ < 2 ^ 64 := by norm_num [P]
  have hnextPrefixBound (limb : Fin 4) :
      slotPrefix natural weights shift mask limb.val block (slots + 1) <
        2 ^ 64 := by
    apply slotPrefix_lt_u64 natural weights hnatural hweights shift mask
      limb.val block (slots + 1) hmask limb.isLt (by omega) (by omega)
  let product (limb : Fin 4) : Std.U64 :=
    Std.U64.wrapping_mul
      (core.convert.num.FromU64U32.from (qm31Limb weight limb)) value
  have hproduct (limb : Fin 4) : (product limb).val =
      deployedLeft natural shift (4 * block + slots) *
        deployedWeight weights shift mask limb.val (4 * block + slots) := by
    unfold product
    rw [u64_wrapping_mul_exact]
    · rw [show (core.convert.num.FromU64U32.from
          (qm31Limb weight limb) : Std.U64).val =
          (qm31Limb weight limb).val by simp,
        hvalue, hmWord, hweightWord]
      exact Nat.mul_comm _ _
    · rw [show (core.convert.num.FromU64U32.from
          (qm31Limb weight limb) : Std.U64).val =
          (qm31Limb weight limb).val by simp, hvalue]
      simpa [Nat.mul_comm] using hproductBound limb
  let nextValue (limb : Fin 4) : Std.U64 :=
    Std.U64.wrapping_add (rawEntry raw limb) (product limb)
  have hnextValue (limb : Fin 4) : (nextValue limb).val =
      slotPrefix natural weights shift mask limb.val block (slots + 1) := by
    unfold nextValue
    rw [u64_wrapping_add_exact]
    · rw [hraw, hproduct, slotPrefix_succ]
    · rw [hraw, hproduct, ← slotPrefix_succ]
      exact hnextPrefixBound limb
  let raw0 := raw.set 0#usize (nextValue 0)
  let raw1 := raw0.set 1#usize (nextValue 1)
  let raw2 := raw1.set 2#usize (nextValue 2)
  let raw3 := raw2.set 3#usize (nextValue 3)
  have hraw3 (limb : Fin 4) : (rawEntry raw3 limb).val =
      slotPrefix natural weights shift mask limb.val block (slots + 1) := by
    have hcases : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by
      omega
    rcases hcases with h | h | h | h
    · subst limb
      unfold raw3 raw2 raw1 raw0
      rw [rawEntry_set_other _ 3#usize _ 0 (by norm_num),
        rawEntry_set_other _ 2#usize _ 0 (by norm_num),
        rawEntry_set_other _ 1#usize _ 0 (by norm_num),
        rawEntry_set_zero]
      exact hnextValue 0
    · subst limb
      unfold raw3 raw2 raw1 raw0
      rw [rawEntry_set_other _ 3#usize _ 1 (by norm_num),
        rawEntry_set_other _ 2#usize _ 1 (by norm_num),
        rawEntry_set_one]
      exact hnextValue 1
    · subst limb
      unfold raw3 raw2 raw1 raw0
      rw [rawEntry_set_other _ 3#usize _ 2 (by norm_num),
        rawEntry_set_two]
      exact hnextValue 2
    · subst limb
      unfold raw3 raw2 raw1 raw0
      rw [rawEntry_set_three]
      exact hnextValue 3
  let indexNext := Std.Usize.wrapping_add index 2#usize
  have hindexNext : indexNext.val = index.val + 2 := by
    apply usize_wrapping_add_two_val
    have := usize_size_large
    omega
  have hcondition : index < blockEnd :=
    (UScalar.lt_equiv _ _).2 ((source_index_lt_blockEnd_iff natural weights
      shift mask block slots blockEnd index raw
      ⟨hblock, hblockActive, hslots, hprocessed,
        hindex, hblockEnd, hraw⟩).2 hcontinue)
  refine ⟨(indexNext, raw3), ?_, ?_⟩
  · unfold singleInnerBody
    unfold
      v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0_loop0.body
    rw [if_pos hcondition]
    change (do
      let weight1 ← Array.index_usize weights xorIndex
      let m1 ← Array.index_usize natural index
      let value1 ← lift (core.convert.num.FromU64U32.from m1)
      let i2 ← lift (core.convert.num.FromU64U32.from weight1.c0.a)
      let i3 ← lift (Std.U64.wrapping_mul i2 value1)
      let i4 ← Array.index_usize raw 0#usize
      let i5 ← lift (Std.U64.wrapping_add i4 i3)
      let raw4 ← Array.update raw 0#usize i5
      let i6 ← lift (core.convert.num.FromU64U32.from weight1.c0.b)
      let i7 ← lift (Std.U64.wrapping_mul i6 value1)
      let i8 ← Array.index_usize raw4 1#usize
      let i9 ← lift (Std.U64.wrapping_add i8 i7)
      let raw5 ← Array.update raw4 1#usize i9
      let i10 ← lift (core.convert.num.FromU64U32.from weight1.c1.a)
      let i11 ← lift (Std.U64.wrapping_mul i10 value1)
      let i12 ← Array.index_usize raw5 2#usize
      let i13 ← lift (Std.U64.wrapping_add i12 i11)
      let raw6 ← Array.update raw5 2#usize i13
      let i14 ← lift (core.convert.num.FromU64U32.from weight1.c1.b)
      let i15 ← lift (Std.U64.wrapping_mul i14 value1)
      let i16 ← Array.index_usize raw6 3#usize
      let i17 ← lift (Std.U64.wrapping_add i16 i15)
      let raw7 ← Array.update raw6 3#usize i17
      let index1 ← lift (Std.Usize.wrapping_add index 2#usize)
      ok (cont (index1, raw7))) = _
    rw [hweightCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hmCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_call raw 0#usize (by norm_num)]
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let raw4 ← Array.update raw 0#usize (nextValue 0)
      let i8 ← Array.index_usize raw4 1#usize
      let raw5 ← Array.update raw4 1#usize
        (Std.U64.wrapping_add i8 (product 1))
      let i12 ← Array.index_usize raw5 2#usize
      let raw6 ← Array.update raw5 2#usize
        (Std.U64.wrapping_add i12 (product 2))
      let i16 ← Array.index_usize raw6 3#usize
      let raw7 ← Array.update raw6 3#usize
        (Std.U64.wrapping_add i16 (product 3))
      ok (cont (indexNext, raw7))) = _
    rw [raw_update_call raw 0#usize (by norm_num)]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_call raw0 1#usize (by norm_num)]
    simp only [Aeneas.Std.bind_tc_ok]
    unfold raw0 at ⊢
    rw [rawEntry_set_other raw 0#usize _
      ⟨(1#usize).val, by norm_num⟩ (by norm_num)]
    change (do
      let raw5 ← Array.update raw0 1#usize (nextValue 1)
      let i12 ← Array.index_usize raw5 2#usize
      let raw6 ← Array.update raw5 2#usize
        (Std.U64.wrapping_add i12 (product 2))
      let i16 ← Array.index_usize raw6 3#usize
      let raw7 ← Array.update raw6 3#usize
        (Std.U64.wrapping_add i16 (product 3))
      ok (cont (indexNext, raw7))) = _
    rw [raw_update_call raw0 1#usize (by norm_num)]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_call raw1 2#usize (by norm_num)]
    simp only [Aeneas.Std.bind_tc_ok]
    unfold raw1 raw0 at ⊢
    rw [rawEntry_set_other _ 1#usize _
        ⟨(2#usize).val, by norm_num⟩ (by norm_num),
      rawEntry_set_other _ 0#usize _
        ⟨(2#usize).val, by norm_num⟩ (by norm_num)]
    change (do
      let raw6 ← Array.update raw1 2#usize (nextValue 2)
      let i16 ← Array.index_usize raw6 3#usize
      let raw7 ← Array.update raw6 3#usize
        (Std.U64.wrapping_add i16 (product 3))
      ok (cont (indexNext, raw7))) = _
    rw [raw_update_call raw1 2#usize (by norm_num)]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_call raw2 3#usize (by norm_num)]
    simp only [Aeneas.Std.bind_tc_ok]
    unfold raw2 raw1 raw0 at ⊢
    rw [rawEntry_set_other _ 2#usize _
        ⟨(3#usize).val, by norm_num⟩ (by norm_num),
      rawEntry_set_other _ 1#usize _
        ⟨(3#usize).val, by norm_num⟩ (by norm_num),
      rawEntry_set_other _ 0#usize _
        ⟨(3#usize).val, by norm_num⟩ (by norm_num)]
    change (do
      let raw7 ← Array.update raw2 3#usize (nextValue 3)
      ok (cont (indexNext, raw7))) = _
    rw [raw_update_call raw2 3#usize (by norm_num)]
    simp only [Aeneas.Std.bind_tc_ok]
    rfl
  · refine ⟨hblock, hblockActive, by omega, by omega, ?_, hblockEnd, hraw3⟩
    rw [hindexNext, hindex]
    omega

private theorem singleInnerBody_done (natural : LocalNatural)
    (weights : LocalWeights) (shift : Fin 12) (runtimeMask : Std.Usize)
    (mask block slots : Nat) (blockEnd index : Std.Usize) (raw : Raw4)
    (hinvariant : SingleInnerInvariant natural weights shift mask block slots
      blockEnd index raw)
    (hstop : ¬ (slots < 4 ∧
      4 * block + slots < deployedSupportCount shift)) :
    singleInnerBody natural weights runtimeMask blockEnd index raw =
      .ok (.done (index, raw)) := by
  have hnlt : ¬ index < blockEnd := by
    intro hlt
    apply hstop
    exact (source_index_lt_blockEnd_iff natural weights shift mask block slots
      blockEnd index raw hinvariant).1 ((UScalar.lt_equiv _ _).1 hlt)
  unfold singleInnerBody
  unfold
    v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0_loop0.body
  rw [if_neg hnlt]

def blockLogicalEnd (shift : Fin 12) (block : Nat) : Nat :=
  Nat.min (4 * (block + 1)) (deployedSupportCount shift)

private theorem singleInnerBody_transition_spec (natural : LocalNatural)
    (weights : LocalWeights) (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (runtimeMask : Std.Usize) (mask block slots : Nat)
    (blockEnd index : Std.Usize) (raw : Raw4)
    (hruntimeMask : runtimeMask.val = mask) (hmask : MaskBound mask)
    (hinvariant : SingleInnerInvariant natural weights shift mask block slots
      blockEnd index raw) :
    ∃ flow,
      singleInnerBody natural weights runtimeMask blockEnd index raw =
        .ok flow ∧
      (match flow with
        | .done result =>
            result.1.val = shift.val % 2 +
              2 * blockLogicalEnd shift block ∧
            ∀ limb : Fin 4,
              (rawEntry result.2 limb).val =
                blockRawAt natural weights shift mask limb.val block
        | .cont next =>
            SingleInnerInvariant natural weights shift mask block (slots + 1)
              blockEnd next.1 next.2 ∧
            4 - (slots + 1) < 4 - slots) := by
  by_cases hcontinue : slots < 4 ∧
      4 * block + slots < deployedSupportCount shift
  · rcases singleInnerBody_step natural weights hnatural hweights shift
      runtimeMask mask block slots blockEnd index raw hruntimeMask hmask
      hinvariant hcontinue with ⟨state, hcall, hstate⟩
    refine ⟨.cont state, hcall, hstate, ?_⟩
    omega
  · have hcall := singleInnerBody_done natural weights shift runtimeMask mask
      block slots blockEnd index raw hinvariant hcontinue
    rcases hinvariant with ⟨hblock, hblockActive, hslots, hprocessed,
      hindex, hblockEnd, hraw⟩
    have hfinal : slots = 4 ∨
        deployedSupportCount shift ≤ 4 * block + slots := by
      omega
    have hlogicalEnd : 4 * block + slots = blockLogicalEnd shift block := by
      unfold blockLogicalEnd
      rcases hfinal with hfull | hterminal
      · subst slots
        have hle : 4 * (block + 1) ≤ deployedSupportCount shift := by omega
        calc
          4 * block + 4 = 4 * (block + 1) := by omega
          _ = Nat.min (4 * (block + 1)) (deployedSupportCount shift) :=
            (Nat.min_eq_left hle).symm
      · have hle : deployedSupportCount shift ≤ 4 * (block + 1) := by
          omega
        calc
          4 * block + slots = deployedSupportCount shift := by omega
          _ = Nat.min (4 * (block + 1)) (deployedSupportCount shift) :=
            (Nat.min_eq_right hle).symm
    refine ⟨.done (index, raw), hcall, ?_, ?_⟩
    · rw [hindex, hlogicalEnd]
    · intro limb
      rw [hraw]
      apply slotPrefix_eq_blockRawAt natural weights shift mask limb.val block
        slots hblock hslots hprocessed hfinal

def SingleInnerStateInvariant (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask block : Nat) (blockEnd : Std.Usize)
    (state : Std.Usize × Raw4) : Prop :=
  ∃ slots,
    SingleInnerInvariant natural weights shift mask block slots blockEnd
      state.1 state.2

theorem singleInnerLoop_spec (natural : LocalNatural) (weights : LocalWeights)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (runtimeMask : Std.Usize) (mask block slots : Nat)
    (blockEnd index : Std.Usize) (raw : Raw4)
    (hruntimeMask : runtimeMask.val = mask) (hmask : MaskBound mask)
    (hinvariant : SingleInnerInvariant natural weights shift mask block slots
      blockEnd index raw) :
    ∃ result : Std.Usize × Raw4,
      singleInnerLoop natural weights runtimeMask index blockEnd raw =
        .ok result ∧
      result.1.val = shift.val % 2 + 2 * blockLogicalEnd shift block ∧
      ∀ limb : Fin 4,
        (rawEntry result.2 limb).val =
          blockRawAt natural weights shift mask limb.val block := by
  have hspec : Aeneas.Std.WP.spec
      (singleInnerLoop natural weights runtimeMask index blockEnd raw)
      (fun result =>
        result.1.val = shift.val % 2 + 2 * blockLogicalEnd shift block ∧
        ∀ limb : Fin 4, (rawEntry result.2 limb).val =
          blockRawAt natural weights shift mask limb.val block) := by
    unfold singleInnerLoop
    unfold
      v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0_loop0
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun state => blockEnd.val - state.1.val)
      (inv := SingleInnerStateInvariant natural weights shift mask block blockEnd)
    · rintro ⟨nextIndex, nextRaw⟩ hstate
      rcases hstate with ⟨nextSlots, hnextInvariant⟩
      simp only
      apply Aeneas.Std.WP.exists_imp_spec
      have htransition := singleInnerBody_transition_spec natural weights
        hnatural hweights shift runtimeMask mask block nextSlots blockEnd
        nextIndex nextRaw hruntimeMask hmask hnextInvariant
      unfold singleInnerBody at htransition
      rcases htransition with ⟨flow, hcall, hpost⟩
      refine ⟨flow, hcall, ?_⟩
      cases flow with
      | done result => exact hpost
      | cont state =>
          have hstateInvariant := hpost.1
          rcases hnextInvariant with ⟨holdBlock, holdActive, holdSlots,
            holdProcessed, holdIndex, holdEnd, holdRaw⟩
          rcases hstateInvariant with ⟨hnewBlock, hnewActive, hnewSlots,
            hnewProcessed, hnewIndex, hnewEnd, hnewRaw⟩
          refine ⟨⟨nextSlots + 1,
            ⟨hnewBlock, hnewActive, hnewSlots, hnewProcessed, hnewIndex,
              hnewEnd, hnewRaw⟩⟩, ?_⟩
          have hcontinue : nextSlots < 4 ∧
              4 * block + nextSlots < deployedSupportCount shift := by
            omega
          have holdLt : nextIndex.val < blockEnd.val :=
            (source_index_lt_blockEnd_iff natural weights shift mask block
              nextSlots blockEnd nextIndex nextRaw
              ⟨holdBlock, holdActive, holdSlots, holdProcessed, holdIndex,
                holdEnd, holdRaw⟩).2 hcontinue
          have hprogress : nextIndex.val < state.1.val := by
            rw [holdIndex, hnewIndex]
            omega
          exact Nat.sub_lt_sub_left holdLt hprogress
    · exact ⟨slots, hinvariant⟩
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨result, hcall, hindex, hraw⟩
  exact ⟨result, hcall, hindex, hraw⟩

theorem blockRawAt_lt_u64 (natural : LocalNatural) (weights : LocalWeights)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (mask limb block : Nat) (hmask : MaskBound mask) (hlimb : limb < 4)
    (hblock : block < 6) :
    blockRawAt natural weights shift mask limb block < 2 ^ 64 := by
  unfold blockRawAt
  rw [dif_pos hblock]
  exact blockRaw_lt_u64 (paddedLeft natural shift)
    (paddedWeight weights shift mask limb)
    (paddedLeft_canonical natural hnatural shift)
    (paddedWeight_canonical weights hweights shift mask limb hmask hlimb)
    ⟨block, hblock⟩

theorem outerPrefix_lt_u64 (natural : LocalNatural) (weights : LocalWeights)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (mask limb blocks : Nat) (hmask : MaskBound mask) (hlimb : limb < 4)
    (hblocks : blocks ≤ 6) :
    outerPrefix natural weights shift mask limb blocks < 2 ^ 64 := by
  have hterm : ∀ block ∈ Finset.range blocks,
      rawReduceU64 (blockRawAt natural weights shift mask limb block) ≤
        P - 1 := by
    intro block hblock
    have hblock6 : block < 6 :=
      (Finset.mem_range.mp hblock).trans_le hblocks
    exact Nat.le_pred_of_lt (rawReduceU64_canonical _
      (blockRawAt_lt_u64 natural weights hnatural hweights shift mask limb
        block hmask hlimb hblock6))
  calc
    outerPrefix natural weights shift mask limb blocks ≤
        ∑ _block ∈ Finset.range blocks, (P - 1) := by
      unfold outerPrefix
      exact Finset.sum_le_sum fun block hblock => hterm block hblock
    _ = blocks * (P - 1) := by simp
    _ ≤ 6 * (P - 1) := Nat.mul_le_mul_right _ hblocks
    _ < 2 ^ 64 := by norm_num [P]

private abbrev singleReduceBody :=
  v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0_loop1.body

private abbrev singleReduceLoop :=
  v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0_loop1

def SingleReduceInvariant (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask block : Nat) (raw sums : Raw4)
    (limb : Std.Usize) : Prop :=
  block < 6 ∧
  limb.val ≤ 4 ∧
  (∀ output : Fin 4, (rawEntry raw output).val =
    blockRawAt natural weights shift mask output.val block) ∧
  ∀ output : Fin 4,
    (rawEntry sums output).val =
      if output.val < limb.val then
        outerPrefix natural weights shift mask output.val (block + 1)
      else outerPrefix natural weights shift mask output.val block

private theorem singleReduceBody_step (natural : LocalNatural)
    (weights : LocalWeights) (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (mask block : Nat) (hmask : MaskBound mask) (raw sums : Raw4)
    (limb : Std.Usize)
    (hinvariant : SingleReduceInvariant natural weights shift mask block raw
      sums limb) (hcontinue : limb.val < 4) :
    ∃ state : Raw4 × Std.Usize,
      singleReduceBody raw sums limb = .ok (.cont state) ∧
      state.2.val = limb.val + 1 ∧
      SingleReduceInvariant natural weights shift mask block raw state.1
        state.2 := by
  rcases hinvariant with ⟨hblock, hlimb4, hraw, hsums⟩
  have hcondition : limb < (Array.to_slice raw).len := by
    apply (UScalar.lt_equiv _ _).2
    simpa using hcontinue
  let limbFin : Fin 4 := ⟨limb.val, hcontinue⟩
  have hrawCall : Array.index_usize raw limb =
      .ok (rawEntry raw limbFin) := raw_index_call raw limb hcontinue
  obtain ⟨reduced, hreduceCall, hreduced⟩ :=
    GoodMatricesCurrent.SourceExtractedField.authentic_reduce_u64_word_spec
      (rawEntry raw limbFin)
  have hrawBound : (rawEntry raw limbFin).val < 2 ^ 64 := by
    rw [hraw]
    exact blockRawAt_lt_u64 natural weights hnatural hweights shift mask
      limb.val block hmask hcontinue hblock
  have hreducedCanonical : reduced.val < P := by
    rw [hreduced]
    exact rawReduceU64_canonical _ hrawBound
  have hreducedValue : reduced.val =
      rawReduceU64 (blockRawAt natural weights shift mask limb.val block) := by
    rw [hreduced, hraw]
  let wideReduced : Std.U64 := core.convert.num.FromU64U32.from reduced
  have hwideReduced : wideReduced.val = reduced.val := by simp [wideReduced]
  have hsumsCall : Array.index_usize sums limb =
      .ok (rawEntry sums limbFin) := raw_index_call sums limb hcontinue
  have hcurrentSum : (rawEntry sums limbFin).val =
      outerPrefix natural weights shift mask limb.val block := by
    rw [hsums]
    simp [limbFin]
  let nextValue := Std.U64.wrapping_add (rawEntry sums limbFin) wideReduced
  have hnextBound : outerPrefix natural weights shift mask limb.val
      (block + 1) < 2 ^ 64 := by
    apply outerPrefix_lt_u64 natural weights hnatural hweights shift mask
      limb.val (block + 1) hmask hcontinue
    omega
  have hnextValue : nextValue.val =
      outerPrefix natural weights shift mask limb.val (block + 1) := by
    unfold nextValue
    rw [u64_wrapping_add_exact]
    · rw [hcurrentSum, hwideReduced, hreducedValue, outerPrefix_succ]
    · rw [hcurrentSum, hwideReduced, hreducedValue, ← outerPrefix_succ]
      exact hnextBound
  let sumsNext := sums.set limb nextValue
  have hsumsNext (output : Fin 4) : (rawEntry sumsNext output).val =
      if output.val < limb.val + 1 then
        outerPrefix natural weights shift mask output.val (block + 1)
      else outerPrefix natural weights shift mask output.val block := by
    by_cases heq : output.val = limb.val
    · have hout : output = limbFin := Fin.ext heq
      subst output
      unfold sumsNext
      have hsame : rawEntry (sums.set limb nextValue) limbFin = nextValue := by
        unfold rawEntry
        exact List.getElem_set_self (by
          simp only [List.length_set]
          rw [sums.property]
          exact hcontinue)
      rw [hsame, hnextValue]
      simp [limbFin]
    · unfold sumsNext
      rw [rawEntry_set_other sums limb nextValue output (by omega), hsums]
      by_cases hbefore : output.val < limb.val
      · have hbeforeNext : output.val < limb.val + 1 := by omega
        simp [hbefore, hbeforeNext]
      · have hafter : limb.val + 1 ≤ output.val := by omega
        simp [Nat.not_lt.mpr hafter, hbefore]
  have hupdate : Array.update sums limb nextValue = .ok sumsNext := by
    exact raw_update_call sums limb hcontinue nextValue
  let limbNext := Std.Usize.wrapping_add limb 1#usize
  have hlimbNext : limbNext.val = limb.val + 1 := by
    apply usize_wrapping_add_one_val
    have := usize_size_large
    omega
  refine ⟨(sumsNext, limbNext), ?_, hlimbNext, ?_⟩
  · unfold singleReduceBody
    unfold
      v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0_loop1.body
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
    rw [if_pos hcondition]
    rw [hrawCall]
    simp only [Aeneas.Std.bind_tc_ok]
    unfold aspis_core.field.M31.reduce_u64
    rw [hreduceCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hsumsCall]
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let next ← Array.update sums limb nextValue
      ok (cont (next, limbNext))) = _
    rw [hupdate]
    rfl
  · refine ⟨hblock, by rw [hlimbNext]; omega, hraw, ?_⟩
    intro output
    rw [hlimbNext]
    exact hsumsNext output

private theorem singleReduceBody_done (raw sums : Raw4) (limb : Std.Usize)
    (hlimb : limb.val = 4) :
    singleReduceBody raw sums limb = .ok (.done sums) := by
  have hcondition : ¬ limb < (Array.to_slice raw).len := by
    intro hlt
    have hltNat := (UScalar.lt_equiv _ _).1 hlt
    norm_num at hltNat
    omega
  unfold singleReduceBody
  unfold
    v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0_loop1.body
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [if_neg hcondition]

private theorem singleReduceBody_transition_spec (natural : LocalNatural)
    (weights : LocalWeights) (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (mask block : Nat) (hmask : MaskBound mask) (raw sums : Raw4)
    (limb : Std.Usize)
    (hinvariant : SingleReduceInvariant natural weights shift mask block raw
      sums limb) :
    ∃ flow, singleReduceBody raw sums limb = .ok flow ∧
      (match flow with
        | .done result => ∀ output : Fin 4,
            (rawEntry result output).val =
              outerPrefix natural weights shift mask output.val (block + 1)
        | .cont next =>
            SingleReduceInvariant natural weights shift mask block raw next.1
              next.2 ∧
            4 - next.2.val < 4 - limb.val) := by
  by_cases hcontinue : limb.val < 4
  · rcases singleReduceBody_step natural weights hnatural hweights shift
      mask block hmask raw sums limb hinvariant hcontinue with
      ⟨state, hcall, hnext, hstate⟩
    refine ⟨.cont state, hcall, hstate, ?_⟩
    rw [hnext]
    omega
  · have hfinal : limb.val = 4 := by
      have hle := hinvariant.2.1
      omega
    have hcall := singleReduceBody_done raw sums limb hfinal
    refine ⟨.done sums, hcall, ?_⟩
    intro output
    rw [hinvariant.2.2.2 output, hfinal]
    simp

theorem singleReduceLoop_spec (natural : LocalNatural) (weights : LocalWeights)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (mask block : Nat) (hmask : MaskBound mask) (raw sums : Raw4)
    (limb : Std.Usize)
    (hinvariant : SingleReduceInvariant natural weights shift mask block raw
      sums limb) :
    ∃ result : Raw4,
      singleReduceLoop sums raw limb = .ok result ∧
      ∀ output : Fin 4, (rawEntry result output).val =
        outerPrefix natural weights shift mask output.val (block + 1) := by
  have hspec : Aeneas.Std.WP.spec (singleReduceLoop sums raw limb)
      (fun result => ∀ output : Fin 4, (rawEntry result output).val =
        outerPrefix natural weights shift mask output.val (block + 1)) := by
    unfold singleReduceLoop
    unfold
      v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0_loop1
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun state => 4 - state.2.val)
      (inv := fun state => SingleReduceInvariant natural weights shift mask block
        raw state.1 state.2)
    · rintro ⟨nextSums, nextLimb⟩ hstate
      simp only
      apply Aeneas.Std.WP.exists_imp_spec
      have htransition := singleReduceBody_transition_spec natural weights
        hnatural hweights shift mask block hmask raw nextSums nextLimb hstate
      unfold singleReduceBody at htransition
      rcases htransition with ⟨flow, hcall, hpost⟩
      exact ⟨flow, hcall, by cases flow <;> exact hpost⟩
    · exact hinvariant
  rcases Aeneas.Std.WP.spec_imp_exists hspec with ⟨result, hcall, hresult⟩
  exact ⟨result, hcall, hresult⟩

theorem blockRawAt_inactive (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask limb block : Nat) (hblock : block < 6)
    (hinactive : deployedSupportCount shift ≤ 4 * block) :
    blockRawAt natural weights shift mask limb block = 0 := by
  rw [blockRawAt_eq_sum_range_four natural weights shift mask limb block hblock]
  apply Finset.sum_eq_zero
  intro slot hslot
  rw [if_neg]
  omega

theorem outerPrefix_final (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask limb blocks : Nat) (hblocks : blocks ≤ 6)
    (hfinal : deployedSupportCount shift ≤ 4 * blocks) :
    outerPrefix natural weights shift mask limb blocks =
      outerPrefix natural weights shift mask limb 6 := by
  unfold outerPrefix
  apply Finset.sum_subset
  · intro block hblock
    simp only [Finset.mem_range] at hblock ⊢
    omega
  · intro block hblock6 hblock
    have hblockLt := Finset.mem_range.mp hblock6
    have hblocksLe : blocks ≤ block := by simpa using hblock
    have hinactive : deployedSupportCount shift ≤ 4 * block := by omega
    rw [blockRawAt_inactive natural weights shift mask limb block hblockLt
      hinactive]
    rfl

private abbrev singleOuterBody :=
  v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0.body

private abbrev singleOuterLoop :=
  v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0

def SingleOuterInvariant (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask : Nat) (supportEnd : Std.Usize)
    (sums : Raw4) (index : Std.Usize) : Prop :=
  ∃ block, block ≤ 6 ∧
    index.val = shift.val % 2 +
      2 * Nat.min (4 * block) (deployedSupportCount shift) ∧
    supportEnd.val = deployedSupportEnd shift ∧
    ∀ limb : Fin 4, (rawEntry sums limb).val =
      outerPrefix natural weights shift mask limb.val block

private theorem outer_index_lt_supportEnd_iff (natural : LocalNatural)
    (weights : LocalWeights) (shift : Fin 12) (mask : Nat)
    (supportEnd : Std.Usize) (sums : Raw4) (index : Std.Usize)
    (hinvariant : SingleOuterInvariant natural weights shift mask supportEnd
      sums index) :
    index.val < supportEnd.val ↔
      ∃ block, block ≤ 6 ∧
        index.val = shift.val % 2 + 2 * (4 * block) ∧
        4 * block < deployedSupportCount shift ∧
        (∀ limb : Fin 4, (rawEntry sums limb).val =
          outerPrefix natural weights shift mask limb.val block) := by
  rcases hinvariant with ⟨block, hblock, hindex, hend, hsums⟩
  constructor
  · intro hlt
    have hactive : 4 * block < deployedSupportCount shift := by
      rw [hend, hindex] at hlt
      have hshape := support_runtime_shape shift
      by_contra hnot
      have hle : deployedSupportCount shift ≤ 4 * block := by omega
      have hmin : (4 * block).min (deployedSupportCount shift) =
          deployedSupportCount shift := by
        exact Nat.min_eq_right hle
      rw [hmin] at hlt
      omega
    have hmin : (4 * block).min (deployedSupportCount shift) = 4 * block := by
      exact Nat.min_eq_left (Nat.le_of_lt hactive)
    refine ⟨block, hblock, ?_, hactive, hsums⟩
    rw [hindex, hmin]
  · rintro ⟨other, _hother, hindexOther, hactive, _hsumsOther⟩
    rw [hend, hindexOther]
    have hendIndex := deployedSupportIndex_lt_end shift (4 * other) hactive
    simpa [deployedSupportIndex] using hendIndex

private theorem repeated_zero_raw (limb : Fin 4) :
    (rawEntry (Array.repeat 4#usize 0#u64) limb).val = 0 := by
  unfold rawEntry Array.repeat
  rw [List.getElem_replicate]
  rfl

private theorem singleOuterBody_step (natural : LocalNatural)
    (weights : LocalWeights) (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (runtimeMask : Std.Usize) (mask : Nat) (supportEnd : Std.Usize)
    (sums : Raw4) (index : Std.Usize)
    (hruntimeMask : runtimeMask.val = mask) (hmask : MaskBound mask)
    (hinvariant : SingleOuterInvariant natural weights shift mask supportEnd
      sums index) (hcontinue : index.val < supportEnd.val) :
    ∃ state : Raw4 × Std.Usize,
      singleOuterBody natural weights runtimeMask supportEnd sums index =
        .ok (.cont state) ∧
      index.val < state.2.val ∧
      SingleOuterInvariant natural weights shift mask supportEnd state.1
        state.2 := by
  rcases (outer_index_lt_supportEnd_iff natural weights shift mask supportEnd
      sums index hinvariant).1 hcontinue with
    ⟨block, hblock6, hindex, hblockActive, hsums⟩
  have hblock : block < 6 := by
    have hcount := (deployedSupportCount_bounds shift).2
    omega
  have hcondition : index < supportEnd :=
    (UScalar.lt_equiv _ _).2 hcontinue
  let plusEight := Std.Usize.wrapping_add index 8#usize
  have hplusEight : plusEight.val = index.val + 8 := by
    apply usize_wrapping_add_eight_val
    have := usize_size_large
    have hindexBound : index.val < 64 := by
      rw [hindex]
      have hcount := (deployedSupportCount_bounds shift).2
      have hshift := shift.isLt
      omega
    omega
  obtain ⟨blockEnd, hblockEndCall, hblockEnd⟩ :=
    usize_min_spec plusEight supportEnd
  have hsupportEnd : supportEnd.val = deployedSupportEnd shift :=
    hinvariant.choose_spec.2.2.1
  have hblockEndValue : blockEnd.val = Nat.min
      (shift.val % 2 + 2 * (4 * block) + 8)
      (deployedSupportEnd shift) := by
    rw [hblockEnd, hplusEight, hindex, hsupportEnd]
  let zeroRaw : Raw4 := Array.repeat 4#usize 0#u64
  have hinnerInvariant : SingleInnerInvariant natural weights shift mask block 0
      blockEnd index zeroRaw := by
    refine ⟨hblock, hblockActive, by norm_num, by omega, hindex,
      hblockEndValue, ?_⟩
    intro limb
    rw [repeated_zero_raw]
    simp [slotPrefix]
  rcases singleInnerLoop_spec natural weights hnatural hweights shift
      runtimeMask mask block 0 blockEnd index zeroRaw hruntimeMask hmask
      hinnerInvariant with ⟨inner, hinnerCall, hinnerIndex, hinnerRaw⟩
  have hreduceInvariant : SingleReduceInvariant natural weights shift mask block
      inner.2 sums 0#usize := by
    refine ⟨hblock, by norm_num, hinnerRaw, ?_⟩
    intro limb
    rw [hsums]
    simp
  rcases singleReduceLoop_spec natural weights hnatural hweights shift mask block
      hmask inner.2 sums 0#usize hreduceInvariant with
    ⟨nextSums, hreduceCall, hnextSums⟩
  have hprogress : index.val < inner.1.val := by
    rw [hindex, hinnerIndex]
    unfold blockLogicalEnd
    have hminGrowth : 4 * block <
        Nat.min (4 * (block + 1)) (deployedSupportCount shift) := by
      apply lt_min
      · omega
      · exact hblockActive
    omega
  refine ⟨(nextSums, inner.1), ?_, hprogress, ?_⟩
  · unfold singleOuterBody
    unfold
      v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0.body
    rw [if_pos hcondition]
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
    change (do
      let block_end ← core.cmp.min core.cmp.OrdUsize plusEight supportEnd
      let innerResult ← singleInnerLoop natural weights runtimeMask index
        block_end zeroRaw
      let sums1 ← singleReduceLoop sums innerResult.2 0#usize
      ok (cont (sums1, innerResult.1))) = _
    rw [hblockEndCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hinnerCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hreduceCall]
    simp only [Aeneas.Std.bind_tc_ok]
  · refine ⟨block + 1, by omega, ?_, hsupportEnd, hnextSums⟩
    rw [hinnerIndex]
    rfl

private theorem singleOuterBody_done (natural : LocalNatural)
    (weights : LocalWeights) (runtimeMask : Std.Usize)
    (supportEnd : Std.Usize) (sums : Raw4) (index : Std.Usize)
    (hstop : ¬ index.val < supportEnd.val) :
    singleOuterBody natural weights runtimeMask supportEnd sums index =
      .ok (.done sums) := by
  have hcondition : ¬ index < supportEnd := by
    intro hlt
    exact hstop ((UScalar.lt_equiv _ _).1 hlt)
  unfold singleOuterBody
  unfold
    v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0.body
  rw [if_neg hcondition]

private theorem singleOuterBody_transition_spec (natural : LocalNatural)
    (weights : LocalWeights) (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (runtimeMask : Std.Usize) (mask : Nat) (supportEnd : Std.Usize)
    (sums : Raw4) (index : Std.Usize)
    (hruntimeMask : runtimeMask.val = mask) (hmask : MaskBound mask)
    (hinvariant : SingleOuterInvariant natural weights shift mask supportEnd
      sums index) :
    ∃ flow, singleOuterBody natural weights runtimeMask supportEnd sums index =
        .ok flow ∧
      (match flow with
        | .done result => ∀ limb : Fin 4, (rawEntry result limb).val =
            outerPrefix natural weights shift mask limb.val 6
        | .cont next =>
            SingleOuterInvariant natural weights shift mask supportEnd next.1
              next.2 ∧
            supportEnd.val - next.2.val < supportEnd.val - index.val) := by
  by_cases hcontinue : index.val < supportEnd.val
  · rcases singleOuterBody_step natural weights hnatural hweights shift
      runtimeMask mask supportEnd sums index hruntimeMask hmask hinvariant
      hcontinue with ⟨state, hcall, hprogress, hstate⟩
    refine ⟨.cont state, hcall, hstate, ?_⟩
    exact Nat.sub_lt_sub_left hcontinue hprogress
  · have hcall := singleOuterBody_done natural weights runtimeMask supportEnd
      sums index hcontinue
    rcases hinvariant with ⟨block, hblocks, hindex, hend, hsums⟩
    have hfinal : deployedSupportCount shift ≤ 4 * block := by
      by_contra hnot
      have hactive : 4 * block < deployedSupportCount shift := by omega
      have hmin : (4 * block).min (deployedSupportCount shift) = 4 * block := by
        exact Nat.min_eq_left (Nat.le_of_lt hactive)
      apply hcontinue
      rw [hindex, hmin, hend]
      have hlt := deployedSupportIndex_lt_end shift (4 * block) hactive
      simpa [deployedSupportIndex] using hlt
    refine ⟨.done sums, hcall, ?_⟩
    intro limb
    rw [hsums]
    exact outerPrefix_final natural weights shift mask limb.val block hblocks
      hfinal

theorem singleOuterLoop_spec (natural : LocalNatural) (weights : LocalWeights)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (runtimeMask : Std.Usize) (mask : Nat) (supportEnd : Std.Usize)
    (sums : Raw4) (index : Std.Usize)
    (hruntimeMask : runtimeMask.val = mask) (hmask : MaskBound mask)
    (hinvariant : SingleOuterInvariant natural weights shift mask supportEnd
      sums index) :
    ∃ result : Raw4,
      singleOuterLoop natural weights runtimeMask supportEnd sums index =
        .ok result ∧
      ∀ limb : Fin 4, (rawEntry result limb).val =
        outerPrefix natural weights shift mask limb.val 6 := by
  have hspec : Aeneas.Std.WP.spec
      (singleOuterLoop natural weights runtimeMask supportEnd sums index)
      (fun result => ∀ limb : Fin 4, (rawEntry result limb).val =
        outerPrefix natural weights shift mask limb.val 6) := by
    unfold singleOuterLoop
    unfold v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_loop0
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun state => supportEnd.val - state.2.val)
      (inv := fun state => SingleOuterInvariant natural weights shift mask
        supportEnd state.1 state.2)
    · rintro ⟨nextSums, nextIndex⟩ hstate
      simp only
      apply Aeneas.Std.WP.exists_imp_spec
      have htransition := singleOuterBody_transition_spec natural weights
        hnatural hweights shift runtimeMask mask supportEnd nextSums nextIndex
        hruntimeMask hmask hstate
      unfold singleOuterBody at htransition
      rcases htransition with ⟨flow, hcall, hpost⟩
      exact ⟨flow, hcall, by cases flow <;> exact hpost⟩
    · exact hinvariant
  rcases Aeneas.Std.WP.spec_imp_exists hspec with ⟨result, hcall, hresult⟩
  exact ⟨result, hcall, hresult⟩

theorem outerPrefix_six_eq_outerRaw (natural : LocalNatural)
    (weights : LocalWeights) (shift : Fin 12) (mask limb : Nat) :
    outerPrefix natural weights shift mask limb 6 =
      outerRaw (paddedLeft natural shift)
        (paddedWeight weights shift mask limb) := by
  unfold outerPrefix outerRaw blockReduced
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro block hblock
  have hblock6 := Finset.mem_range.mp hblock
  simp [blockRawAt, hblock6]

theorem deployedBatchedLimb_eq_reduce_outerPrefix (natural : LocalNatural)
    (weights : LocalWeights) (shift : Fin 12) (mask limb : Nat) :
    deployedBatchedLimb natural weights shift mask limb =
      rawReduceU64 (outerPrefix natural weights shift mask limb 6) := by
  unfold deployedBatchedLimb batchedDot24
  rw [outerPrefix_six_eq_outerRaw]

@[simp] theorem usize_and_one_val (index : Std.Usize) :
    (index &&& 1#usize).val = index.val % 2 := by
  change index.val &&& 1 = index.val % 2
  exact Nat.and_one_is_mod index.val

theorem evaluate_shifted_in_aligned_block_exact_spec (natural : LocalNatural)
    (weights : LocalWeights) (runtimeShift runtimeMask : Std.Usize)
    (shift : Fin 12) (mask : Nat)
    (hruntimeShift : runtimeShift.val = shift.val)
    (hruntimeMask : runtimeMask.val = mask)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (hmask : MaskBound mask) :
    ∃ result : LocalQM31,
      v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block natural
        runtimeShift weights runtimeMask = .ok result ∧
      CanonicalLocalQM31 result ∧
      qm31ToExact result = deployedBatchedQM31 natural weights shift mask := by
  let degreePlusShift := Std.Usize.wrapping_add
    v5_cu_probe.good_gate_probe.KERNEL_DEGREE runtimeShift
  have hdegreePlusShift : degreePlusShift.val = 36 + shift.val := by
    unfold degreePlusShift
    rw [Std.Usize.wrapping_add_val_eq,
      v5_cu_probe.good_gate_probe.KERNEL_DEGREE, hruntimeShift]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits, hp] at ⊢ <;>
      omega
  let supportEnd := Std.Usize.wrapping_add degreePlusShift 1#usize
  have hsupportEnd : supportEnd.val = deployedSupportEnd shift := by
    unfold supportEnd
    rw [usize_wrapping_add_one_val]
    · rw [hdegreePlusShift]
      unfold deployedSupportEnd
      omega
    · rw [hdegreePlusShift]
      have := usize_size_large
      omega
  let zeroSums : Raw4 := Array.repeat 4#usize 0#u64
  let startIndex := runtimeShift &&& 1#usize
  have hstartIndex : startIndex.val = shift.val % 2 := by
    unfold startIndex
    rw [usize_and_one_val, hruntimeShift]
  have houterInvariant : SingleOuterInvariant natural weights shift mask
      supportEnd zeroSums startIndex := by
    refine ⟨0, by norm_num, ?_, hsupportEnd, ?_⟩
    · rw [hstartIndex]
      norm_num
    · intro limb
      rw [repeated_zero_raw]
      simp [outerPrefix]
  rcases singleOuterLoop_spec natural weights hnatural hweights shift
      runtimeMask mask supportEnd zeroSums startIndex hruntimeMask hmask
      houterInvariant with ⟨sums, hloop, hsums⟩
  have hsumsBound (limb : Fin 4) : (rawEntry sums limb).val < 2 ^ 64 := by
    rw [hsums]
    exact outerPrefix_lt_u64 natural weights hnatural hweights shift mask
      limb.val 6 hmask limb.isLt (by norm_num)
  have reduceSpec (limb : Fin 4) : ∃ reduced : LocalM31,
      aspis_core.field.M31.reduce_u64 (rawEntry sums limb) = .ok reduced ∧
      reduced.val < P ∧
      reduced.val = deployedBatchedLimb natural weights shift mask limb.val := by
    rcases GoodMatricesCurrent.SourceExtractedField.authentic_reduce_u64_word_spec
        (rawEntry sums limb) with ⟨reduced, hcall, hvalue⟩
    refine ⟨reduced, hcall, ?_, ?_⟩
    · rw [hvalue]
      exact rawReduceU64_canonical _ (hsumsBound limb)
    · rw [hvalue, hsums, deployedBatchedLimb_eq_reduce_outerPrefix]
  rcases reduceSpec 0 with ⟨r0, hr0, hr0Canonical, hr0Value⟩
  rcases reduceSpec 1 with ⟨r1, hr1, hr1Canonical, hr1Value⟩
  rcases reduceSpec 2 with ⟨r2, hr2, hr2Canonical, hr2Value⟩
  rcases reduceSpec 3 with ⟨r3, hr3, hr3Canonical, hr3Value⟩
  let result : LocalQM31 :=
    { c0 := { a := r0, b := r1 }, c1 := { a := r2, b := r3 } }
  refine ⟨result, ?_, ?_, ?_⟩
  · unfold v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block
    simp only [Aeneas.Std.lift]
    change (do
      let sums1 ← singleOuterLoop natural weights runtimeMask supportEnd
        zeroSums startIndex
      let i1 ← Array.index_usize sums1 0#usize
      let m ← aspis_core.field.M31.reduce_u64 i1
      let i2 ← Array.index_usize sums1 1#usize
      let m1 ← aspis_core.field.M31.reduce_u64 i2
      let c ← aspis_core.field.CM31.new m m1
      let i3 ← Array.index_usize sums1 2#usize
      let m2 ← aspis_core.field.M31.reduce_u64 i3
      let i4 ← Array.index_usize sums1 3#usize
      let m3 ← aspis_core.field.M31.reduce_u64 i4
      let c1 ← aspis_core.field.CM31.new m2 m3
      ok ({ c0 := c, c1 } : LocalQM31)) = _
    rw [hloop]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_zero_call sums]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hr0]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_one_call sums]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hr1]
    simp only [Aeneas.Std.bind_tc_ok]
    unfold aspis_core.field.CM31.new
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_two_call sums]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hr2]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_three_call sums]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hr3]
    rfl
  · exact ⟨⟨hr0Canonical, hr1Canonical⟩,
      ⟨hr2Canonical, hr3Canonical⟩⟩
  · unfold result qm31ToExact cm31ToExact deployedBatchedQM31
    rw [hr0Value, hr1Value, hr2Value, hr3Value]
    norm_num

abbrev fourLimbUpdate (weight : LocalQM31) (value : Std.U64) (raw : Raw4) :
    Result Raw4 := do
  let p0 := Std.U64.wrapping_mul
    (core.convert.num.FromU64U32.from weight.c0.a) value
  let r0 ← Array.index_usize raw 0#usize
  let n0 := Std.U64.wrapping_add r0 p0
  let raw0 ← Array.update raw 0#usize n0
  let p1 := Std.U64.wrapping_mul
    (core.convert.num.FromU64U32.from weight.c0.b) value
  let r1 ← Array.index_usize raw0 1#usize
  let n1 := Std.U64.wrapping_add r1 p1
  let raw1 ← Array.update raw0 1#usize n1
  let p2 := Std.U64.wrapping_mul
    (core.convert.num.FromU64U32.from weight.c1.a) value
  let r2 ← Array.index_usize raw1 2#usize
  let n2 := Std.U64.wrapping_add r2 p2
  let raw2 ← Array.update raw1 2#usize n2
  let p3 := Std.U64.wrapping_mul
    (core.convert.num.FromU64U32.from weight.c1.b) value
  let r3 ← Array.index_usize raw2 3#usize
  let n3 := Std.U64.wrapping_add r3 p3
  Array.update raw2 3#usize n3

def fourLimbUpdatedArray (weight : LocalQM31) (value : Std.U64)
    (raw : Raw4) : Raw4 :=
  let product (limb : Fin 4) := Std.U64.wrapping_mul
    (core.convert.num.FromU64U32.from (qm31Limb weight limb)) value
  let nextValue (limb : Fin 4) :=
    Std.U64.wrapping_add (rawEntry raw limb) (product limb)
  let raw0 := raw.set 0#usize (nextValue 0)
  let raw1 := raw0.set 1#usize (nextValue 1)
  let raw2 := raw1.set 2#usize (nextValue 2)
  raw2.set 3#usize (nextValue 3)

theorem fourLimbUpdate_spec (weight : LocalQM31) (value : Std.U64)
    (raw : Raw4)
    (hbound : ∀ limb : Fin 4,
      (qm31Limb weight limb).val * value.val < 2 ^ 64 ∧
      (rawEntry raw limb).val +
        (qm31Limb weight limb).val * value.val < 2 ^ 64) :
    fourLimbUpdate weight value raw =
        .ok (fourLimbUpdatedArray weight value raw) ∧
      ∀ limb : Fin 4,
        (rawEntry (fourLimbUpdatedArray weight value raw) limb).val =
        (rawEntry raw limb).val +
          (qm31Limb weight limb).val * value.val := by
  let product (limb : Fin 4) := Std.U64.wrapping_mul
    (core.convert.num.FromU64U32.from (qm31Limb weight limb)) value
  have hproduct (limb : Fin 4) : (product limb).val =
      (qm31Limb weight limb).val * value.val := by
    unfold product
    rw [u64_wrapping_mul_exact]
    · simp
    · simpa using (hbound limb).1
  let nextValue (limb : Fin 4) :=
    Std.U64.wrapping_add (rawEntry raw limb) (product limb)
  have hnextValue (limb : Fin 4) : (nextValue limb).val =
      (rawEntry raw limb).val +
        (qm31Limb weight limb).val * value.val := by
    unfold nextValue
    rw [u64_wrapping_add_exact]
    · rw [hproduct]
    · rw [hproduct]
      exact (hbound limb).2
  let raw0 := raw.set 0#usize (nextValue 0)
  let raw1 := raw0.set 1#usize (nextValue 1)
  let raw2 := raw1.set 2#usize (nextValue 2)
  let raw3 := raw2.set 3#usize (nextValue 3)
  have hraw3 (limb : Fin 4) : (rawEntry raw3 limb).val =
      (rawEntry raw limb).val +
        (qm31Limb weight limb).val * value.val := by
    have hcases : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
    rcases hcases with h | h | h | h
    · subst limb
      unfold raw3 raw2 raw1 raw0
      rw [rawEntry_set_other _ 3#usize _ 0 (by norm_num),
        rawEntry_set_other _ 2#usize _ 0 (by norm_num),
        rawEntry_set_other _ 1#usize _ 0 (by norm_num), rawEntry_set_zero,
        hnextValue]
    · subst limb
      unfold raw3 raw2 raw1 raw0
      rw [rawEntry_set_other _ 3#usize _ 1 (by norm_num),
        rawEntry_set_other _ 2#usize _ 1 (by norm_num), rawEntry_set_one,
        hnextValue]
    · subst limb
      unfold raw3 raw2 raw1 raw0
      rw [rawEntry_set_other _ 3#usize _ 2 (by norm_num), rawEntry_set_two,
        hnextValue]
    · subst limb
      unfold raw3 raw2 raw1 raw0
      rw [rawEntry_set_three, hnextValue]
  have hraw3Expected : raw3 = fourLimbUpdatedArray weight value raw := by
    rfl
  refine ⟨?_, ?_⟩
  · rw [← hraw3Expected]
    unfold fourLimbUpdate
    rw [raw_index_zero_call raw]
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let raw4 ← Array.update raw 0#usize (nextValue 0)
      let r1 ← Array.index_usize raw4 1#usize
      let raw5 ← Array.update raw4 1#usize
        (Std.U64.wrapping_add r1 (product 1))
      let r2 ← Array.index_usize raw5 2#usize
      let raw6 ← Array.update raw5 2#usize
        (Std.U64.wrapping_add r2 (product 2))
      let r3 ← Array.index_usize raw6 3#usize
      Array.update raw6 3#usize (Std.U64.wrapping_add r3 (product 3))) = _
    rw [raw_update_call raw 0#usize (by norm_num)]
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let r1 ← Array.index_usize raw0 1#usize
      let raw5 ← Array.update raw0 1#usize
        (Std.U64.wrapping_add r1 (product 1))
      let r2 ← Array.index_usize raw5 2#usize
      let raw6 ← Array.update raw5 2#usize
        (Std.U64.wrapping_add r2 (product 2))
      let r3 ← Array.index_usize raw6 3#usize
      Array.update raw6 3#usize (Std.U64.wrapping_add r3 (product 3))) = _
    rw [raw_index_one_call raw0]
    simp only [Aeneas.Std.bind_tc_ok]
    unfold raw0 at ⊢
    rw [rawEntry_set_other raw 0#usize _ (1 : Fin 4) (by norm_num)]
    change (do
      let raw5 ← Array.update (raw.set 0#usize (nextValue 0)) 1#usize
        (nextValue 1)
      let r2 ← Array.index_usize raw5 2#usize
      let raw6 ← Array.update raw5 2#usize
        (Std.U64.wrapping_add r2 (product 2))
      let r3 ← Array.index_usize raw6 3#usize
      Array.update raw6 3#usize (Std.U64.wrapping_add r3 (product 3))) = _
    rw [raw_update_call _ 1#usize (by norm_num)]
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let r2 ← Array.index_usize raw1 2#usize
      let raw6 ← Array.update raw1 2#usize
        (Std.U64.wrapping_add r2 (product 2))
      let r3 ← Array.index_usize raw6 3#usize
      Array.update raw6 3#usize (Std.U64.wrapping_add r3 (product 3))) = _
    rw [raw_index_two_call raw1]
    simp only [Aeneas.Std.bind_tc_ok]
    unfold raw1 raw0 at ⊢
    rw [rawEntry_set_other _ 1#usize _ (2 : Fin 4) (by norm_num),
      rawEntry_set_other _ 0#usize _ (2 : Fin 4) (by norm_num)]
    change (do
      let raw6 ← Array.update
        ((raw.set 0#usize (nextValue 0)).set 1#usize (nextValue 1))
        2#usize (nextValue 2)
      let r3 ← Array.index_usize raw6 3#usize
      Array.update raw6 3#usize (Std.U64.wrapping_add r3 (product 3))) = _
    rw [raw_update_call _ 2#usize (by norm_num)]
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let r3 ← Array.index_usize raw2 3#usize
      Array.update raw2 3#usize (Std.U64.wrapping_add r3 (product 3))) = _
    rw [raw_index_three_call raw2]
    simp only [Aeneas.Std.bind_tc_ok]
    unfold raw2 raw1 raw0 at ⊢
    rw [rawEntry_set_other _ 2#usize _ (3 : Fin 4) (by norm_num),
      rawEntry_set_other _ 1#usize _ (3 : Fin 4) (by norm_num),
      rawEntry_set_other _ 0#usize _ (3 : Fin 4) (by norm_num)]
    change Array.update
      (((raw.set 0#usize (nextValue 0)).set 1#usize (nextValue 1)).set
        2#usize (nextValue 2)) 3#usize (nextValue 3) = _
    rw [raw_update_call _ 3#usize (by norm_num)]
  · rw [← hraw3Expected]
    exact hraw3

private abbrev pairedInnerBody :=
  v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0_loop0.body

private abbrev pairedInnerLoop :=
  v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0_loop0

def PairedInnerInvariant (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask block slots : Nat) (blockEnd index : Std.Usize)
    (baseRaw xorRaw : Raw4) : Prop :=
  SingleInnerInvariant natural weights shift 0 block slots blockEnd index
      baseRaw ∧
    SingleInnerInvariant natural weights shift mask block slots blockEnd index
      xorRaw

private theorem pairedInnerBody_step (natural : LocalNatural)
    (weights : LocalWeights) (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (runtimeMask : Std.Usize) (mask block slots : Nat)
    (blockEnd index : Std.Usize) (baseRaw xorRaw : Raw4)
    (hruntimeMask : runtimeMask.val = mask) (hmask : MaskBound mask)
    (hinvariant : PairedInnerInvariant natural weights shift mask block slots
      blockEnd index baseRaw xorRaw)
    (hcontinue : slots < 4 ∧
      4 * block + slots < deployedSupportCount shift) :
    ∃ state : Std.Usize × Raw4 × Raw4,
      pairedInnerBody natural weights runtimeMask blockEnd index baseRaw xorRaw =
        .ok (.cont state) ∧
      PairedInnerInvariant natural weights shift mask block (slots + 1)
        blockEnd state.1 state.2.1 state.2.2 := by
  rcases hinvariant.1 with ⟨hblock, hblockActive, hslots, hprocessed,
    hindex, hblockEnd, hbaseRaw⟩
  rcases hinvariant.2 with ⟨_, _, _, _, _, _, hxorRaw⟩
  have hlogical : 4 * block + slots < deployedSupportCount shift := hcontinue.2
  have hphysical48 := supportIndex_lt_48 shift (4 * block + slots) hlogical
  have hphysicalEq : deployedSupportIndex shift (4 * block + slots) =
      index.val := by
    unfold deployedSupportIndex
    rw [hindex]
  have hindex48 : index.val < 48 := by simpa [hphysicalEq] using hphysical48
  have hindex64 : index.val < 64 := hindex48.trans_le (by norm_num)
  let baseWeight := weightEntry weights ⟨index.val, hindex64⟩
  have hbaseWeightCall : Array.index_usize weights index = .ok baseWeight :=
    weight_index_call weights index hindex64
  have hbaseWeightEq : baseWeight = weightEntry weights
      ⟨deployedSupportIndex shift (4 * block + slots),
        hphysical48.trans_le (by norm_num)⟩ := by
    unfold baseWeight
    apply congrArg (weightEntry weights)
    apply Fin.ext
    exact hphysicalEq.symm
  let xorIndex := index ^^^ runtimeMask
  have hxorIndex : xorIndex.val = Nat.xor index.val mask := by
    unfold xorIndex
    rw [usize_xor_val, hruntimeMask]
  have hxor64 : Nat.xor index.val mask < 64 := hmask _ hindex48
  have hxorIndex64 : xorIndex.val < 64 := by rw [hxorIndex]; exact hxor64
  let xorWeight := weightEntry weights ⟨xorIndex.val, hxorIndex64⟩
  have hxorWeightCall : Array.index_usize weights xorIndex = .ok xorWeight :=
    weight_index_call weights xorIndex hxorIndex64
  have hxorWeightEq : xorWeight = weightEntry weights
      ⟨Nat.xor (deployedSupportIndex shift (4 * block + slots)) mask,
        by rw [hphysicalEq]; exact hxor64⟩ := by
    unfold xorWeight
    apply congrArg (weightEntry weights)
    apply Fin.ext
    calc
      xorIndex.val = Nat.xor index.val mask := hxorIndex
      _ = Nat.xor (deployedSupportIndex shift (4 * block + slots)) mask :=
        congrArg (fun value => Nat.xor value mask) hphysicalEq.symm
  let m := naturalEntry natural ⟨index.val, hindex48⟩
  have hmCall : Array.index_usize natural index = .ok m :=
    natural_index_call natural index hindex48
  have hmEq : m = naturalEntry natural
      ⟨deployedSupportIndex shift (4 * block + slots), hphysical48⟩ := by
    unfold m
    apply congrArg (naturalEntry natural)
    exact Fin.ext hphysicalEq.symm
  let value : Std.U64 := core.convert.num.FromU64U32.from m
  have hvalue : value.val = m.val := by simp [value]
  have hmWord : m.val = deployedLeft natural shift (4 * block + slots) := by
    rw [deployedLeft, naturalWord_active _ _ hphysical48, hmEq]
  have hbaseWeightWord (limb : Fin 4) : (qm31Limb baseWeight limb).val =
      deployedWeight weights shift 0 limb.val (4 * block + slots) := by
    have hxor0 : (deployedSupportIndex shift (4 * block + slots)).xor 0 =
        deployedSupportIndex shift (4 * block + slots) := by
      exact Nat.xor_zero _
    rw [deployedWeight, hxor0,
      weightWord_active weights _ limb.val
        (hphysical48.trans_le (by norm_num)) limb.isLt, hbaseWeightEq]
  have hxorWeightWord (limb : Fin 4) : (qm31Limb xorWeight limb).val =
      deployedWeight weights shift mask limb.val (4 * block + slots) := by
    have hsxor64 : Nat.xor
        (deployedSupportIndex shift (4 * block + slots)) mask < 64 := by
      rw [hphysicalEq]
      exact hxor64
    rw [deployedWeight,
      weightWord_active weights _ limb.val hsxor64 limb.isLt, hxorWeightEq]
  have hbaseBounds (limb : Fin 4) :
      (qm31Limb baseWeight limb).val * value.val < 2 ^ 64 ∧
      (rawEntry baseRaw limb).val +
        (qm31Limb baseWeight limb).val * value.val < 2 ^ 64 := by
    have hnext := slotPrefix_lt_u64 natural weights hnatural hweights shift 0
      limb.val block (slots + 1) mask_zero_bound limb.isLt (by omega)
      (by omega)
    constructor
    · have hleft := deployedLeft_canonical natural hnatural shift _ hlogical
      have hright := deployedWeight_canonical weights hweights shift 0
        limb.val _ mask_zero_bound limb.isLt hlogical
      rw [hbaseWeightWord, hvalue, hmWord]
      calc
        _ ≤ (P - 1) ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul
            (Nat.le_pred_of_lt hright) (Nat.le_pred_of_lt hleft)
        _ < 2 ^ 64 := by norm_num [P]
    · rw [hbaseRaw, hbaseWeightWord, hvalue, hmWord]
      simpa [slotPrefix_succ, Nat.mul_comm] using hnext
  have hxorBounds (limb : Fin 4) :
      (qm31Limb xorWeight limb).val * value.val < 2 ^ 64 ∧
      (rawEntry xorRaw limb).val +
        (qm31Limb xorWeight limb).val * value.val < 2 ^ 64 := by
    have hnext := slotPrefix_lt_u64 natural weights hnatural hweights shift mask
      limb.val block (slots + 1) hmask limb.isLt (by omega) (by omega)
    constructor
    · have hleft := deployedLeft_canonical natural hnatural shift _ hlogical
      have hright := deployedWeight_canonical weights hweights shift mask
        limb.val _ hmask limb.isLt hlogical
      rw [hxorWeightWord, hvalue, hmWord]
      calc
        _ ≤ (P - 1) ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul
            (Nat.le_pred_of_lt hright) (Nat.le_pred_of_lt hleft)
        _ < 2 ^ 64 := by norm_num [P]
    · rw [hxorRaw, hxorWeightWord, hvalue, hmWord]
      simpa [slotPrefix_succ, Nat.mul_comm] using hnext
  let baseNext := fourLimbUpdatedArray baseWeight value baseRaw
  have hbaseSpec := fourLimbUpdate_spec baseWeight value baseRaw hbaseBounds
  have hbaseUpdate : fourLimbUpdate baseWeight value baseRaw = .ok baseNext :=
    hbaseSpec.1
  have hbaseNext := hbaseSpec.2
  let xorNext := fourLimbUpdatedArray xorWeight value xorRaw
  have hxorSpec := fourLimbUpdate_spec xorWeight value xorRaw hxorBounds
  have hxorUpdate : fourLimbUpdate xorWeight value xorRaw = .ok xorNext :=
    hxorSpec.1
  have hxorNext := hxorSpec.2
  have hbaseNextModel (limb : Fin 4) : (rawEntry baseNext limb).val =
      slotPrefix natural weights shift 0 limb.val block (slots + 1) := by
    rw [hbaseNext, hbaseRaw, hbaseWeightWord, hvalue, hmWord]
    simp [slotPrefix_succ, Nat.mul_comm]
  have hxorNextModel (limb : Fin 4) : (rawEntry xorNext limb).val =
      slotPrefix natural weights shift mask limb.val block (slots + 1) := by
    rw [hxorNext, hxorRaw, hxorWeightWord, hvalue, hmWord]
    simp [slotPrefix_succ, Nat.mul_comm]
  let indexNext := Std.Usize.wrapping_add index 2#usize
  have hindexNext : indexNext.val = index.val + 2 := by
    apply usize_wrapping_add_two_val
    have := usize_size_large
    omega
  have hcondition : index < blockEnd :=
    (UScalar.lt_equiv _ _).2
      ((source_index_lt_blockEnd_iff natural weights shift 0 block slots
        blockEnd index baseRaw hinvariant.1).2 hcontinue)
  refine ⟨(indexNext, baseNext, xorNext), ?_, ?_⟩
  · unfold pairedInnerBody
    unfold
      v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0_loop0.body
    rw [if_pos hcondition]
    rw [hbaseWeightCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [show index ^^^ runtimeMask = xorIndex from rfl]
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
    rw [hxorWeightCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hmCall]
    simp only [Aeneas.Std.bind_tc_ok]
    have hcombined : (do
        let base_next ← fourLimbUpdate baseWeight value baseRaw
        let xor_next ← fourLimbUpdate xorWeight value xorRaw
        ok (cont (Std.Usize.wrapping_add index 2#usize, base_next, xor_next))) =
        (.ok (.cont (indexNext, baseNext, xorNext)) :
          Result (ControlFlow (Std.Usize × Raw4 × Raw4)
            (Std.Usize × Raw4 × Raw4))) := by
      rw [hbaseUpdate]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hxorUpdate]
      simp only [Aeneas.Std.bind_tc_ok]
      rfl
    simpa only [fourLimbUpdate, Aeneas.Std.lift, Aeneas.Std.bind_assoc_eq] using hcombined
  · constructor
    · refine ⟨hblock, hblockActive, by omega, by omega, ?_, hblockEnd,
        hbaseNextModel⟩
      rw [hindexNext, hindex]
      omega
    · refine ⟨hblock, hblockActive, by omega, by omega, ?_, hblockEnd,
        hxorNextModel⟩
      rw [hindexNext, hindex]
      omega

private theorem pairedInnerBody_done (natural : LocalNatural)
    (weights : LocalWeights) (runtimeMask : Std.Usize)
    (blockEnd index : Std.Usize) (baseRaw xorRaw : Raw4)
    (hstop : ¬ index.val < blockEnd.val) :
    pairedInnerBody natural weights runtimeMask blockEnd index baseRaw xorRaw =
      .ok (.done (index, baseRaw, xorRaw)) := by
  have hcondition : ¬ index < blockEnd := by
    intro hlt
    exact hstop ((UScalar.lt_equiv _ _).1 hlt)
  unfold pairedInnerBody
  unfold
    v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0_loop0.body
  rw [if_neg hcondition]

private theorem pairedInnerBody_transition_spec (natural : LocalNatural)
    (weights : LocalWeights) (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (runtimeMask : Std.Usize) (mask block slots : Nat)
    (blockEnd index : Std.Usize) (baseRaw xorRaw : Raw4)
    (hruntimeMask : runtimeMask.val = mask) (hmask : MaskBound mask)
    (hinvariant : PairedInnerInvariant natural weights shift mask block slots
      blockEnd index baseRaw xorRaw) :
    ∃ flow,
      pairedInnerBody natural weights runtimeMask blockEnd index baseRaw xorRaw =
        .ok flow ∧
      (match flow with
        | .done result =>
            result.1.val = shift.val % 2 +
              2 * blockLogicalEnd shift block ∧
            (∀ limb : Fin 4,
              (rawEntry result.2.1 limb).val =
                blockRawAt natural weights shift 0 limb.val block) ∧
            ∀ limb : Fin 4,
              (rawEntry result.2.2 limb).val =
                blockRawAt natural weights shift mask limb.val block
        | .cont next =>
            PairedInnerInvariant natural weights shift mask block (slots + 1)
              blockEnd next.1 next.2.1 next.2.2 ∧
            4 - (slots + 1) < 4 - slots) := by
  by_cases hcontinue : slots < 4 ∧
      4 * block + slots < deployedSupportCount shift
  · rcases pairedInnerBody_step natural weights hnatural hweights shift
      runtimeMask mask block slots blockEnd index baseRaw xorRaw hruntimeMask
      hmask hinvariant hcontinue with ⟨state, hcall, hstate⟩
    refine ⟨.cont state, hcall, hstate, ?_⟩
    omega
  · have hstopIndex : ¬ index.val < blockEnd.val := by
      intro hlt
      apply hcontinue
      exact (source_index_lt_blockEnd_iff natural weights shift 0 block slots
        blockEnd index baseRaw hinvariant.1).1 hlt
    have hcall := pairedInnerBody_done natural weights runtimeMask blockEnd index
      baseRaw xorRaw hstopIndex
    rcases hinvariant.1 with ⟨hblock, hblockActive, hslots, hprocessed,
      hindex, _hblockEnd, hbaseRaw⟩
    rcases hinvariant.2 with ⟨_, _, _, _, _, _, hxorRaw⟩
    have hfinal : slots = 4 ∨
        deployedSupportCount shift ≤ 4 * block + slots := by
      omega
    have hlogicalEnd : 4 * block + slots = blockLogicalEnd shift block := by
      unfold blockLogicalEnd
      rcases hfinal with hfull | hterminal
      · subst slots
        have hle : 4 * (block + 1) ≤ deployedSupportCount shift := by omega
        calc
          4 * block + 4 = 4 * (block + 1) := by omega
          _ = Nat.min (4 * (block + 1)) (deployedSupportCount shift) :=
            (Nat.min_eq_left hle).symm
      · have hle : deployedSupportCount shift ≤ 4 * (block + 1) := by
          omega
        calc
          4 * block + slots = deployedSupportCount shift := by omega
          _ = Nat.min (4 * (block + 1)) (deployedSupportCount shift) :=
            (Nat.min_eq_right hle).symm
    refine ⟨.done (index, baseRaw, xorRaw), hcall, ?_, ?_, ?_⟩
    · rw [hindex, hlogicalEnd]
    · intro limb
      rw [hbaseRaw]
      apply slotPrefix_eq_blockRawAt natural weights shift 0 limb.val block
        slots hblock hslots hprocessed hfinal
    · intro limb
      rw [hxorRaw]
      apply slotPrefix_eq_blockRawAt natural weights shift mask limb.val block
        slots hblock hslots hprocessed hfinal

def PairedInnerStateInvariant (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask block : Nat) (blockEnd : Std.Usize)
    (state : Std.Usize × Raw4 × Raw4) : Prop :=
  ∃ slots,
    PairedInnerInvariant natural weights shift mask block slots blockEnd
      state.1 state.2.1 state.2.2

theorem pairedInnerLoop_spec (natural : LocalNatural) (weights : LocalWeights)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (runtimeMask : Std.Usize) (mask block slots : Nat)
    (blockEnd index : Std.Usize) (baseRaw xorRaw : Raw4)
    (hruntimeMask : runtimeMask.val = mask) (hmask : MaskBound mask)
    (hinvariant : PairedInnerInvariant natural weights shift mask block slots
      blockEnd index baseRaw xorRaw) :
    ∃ result : Std.Usize × Raw4 × Raw4,
      pairedInnerLoop natural weights runtimeMask index blockEnd baseRaw xorRaw =
        .ok result ∧
      result.1.val = shift.val % 2 + 2 * blockLogicalEnd shift block ∧
      (∀ limb : Fin 4,
        (rawEntry result.2.1 limb).val =
          blockRawAt natural weights shift 0 limb.val block) ∧
      ∀ limb : Fin 4,
        (rawEntry result.2.2 limb).val =
          blockRawAt natural weights shift mask limb.val block := by
  have hspec : Aeneas.Std.WP.spec
      (pairedInnerLoop natural weights runtimeMask index blockEnd baseRaw xorRaw)
      (fun result =>
        result.1.val = shift.val % 2 + 2 * blockLogicalEnd shift block ∧
        (∀ limb : Fin 4,
          (rawEntry result.2.1 limb).val =
            blockRawAt natural weights shift 0 limb.val block) ∧
        ∀ limb : Fin 4,
          (rawEntry result.2.2 limb).val =
            blockRawAt natural weights shift mask limb.val block) := by
    unfold pairedInnerLoop
    unfold
      v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0_loop0
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun state => blockEnd.val - state.1.val)
      (inv := PairedInnerStateInvariant natural weights shift mask block blockEnd)
    · rintro ⟨nextIndex, nextBase, nextXor⟩ hstate
      rcases hstate with ⟨nextSlots, hnextInvariant⟩
      simp only
      apply Aeneas.Std.WP.exists_imp_spec
      have htransition := pairedInnerBody_transition_spec natural weights
        hnatural hweights shift runtimeMask mask block nextSlots blockEnd
        nextIndex nextBase nextXor hruntimeMask hmask hnextInvariant
      unfold pairedInnerBody at htransition
      rcases htransition with ⟨flow, hcall, hpost⟩
      refine ⟨flow, hcall, ?_⟩
      cases flow with
      | done result => exact hpost
      | cont state =>
          have hstateInvariant := hpost.1
          rcases hnextInvariant.1 with ⟨holdBlock, holdActive, holdSlots,
            holdProcessed, holdIndex, holdEnd, holdRaw⟩
          rcases hstateInvariant.1 with ⟨hnewBlock, hnewActive, hnewSlots,
            hnewProcessed, hnewIndex, hnewEnd, hnewRaw⟩
          refine ⟨⟨nextSlots + 1, hstateInvariant⟩, ?_⟩
          have hcontinue : nextSlots < 4 ∧
              4 * block + nextSlots < deployedSupportCount shift := by
            omega
          have holdLt : nextIndex.val < blockEnd.val :=
            (source_index_lt_blockEnd_iff natural weights shift 0 block
              nextSlots blockEnd nextIndex nextBase
              ⟨holdBlock, holdActive, holdSlots, holdProcessed, holdIndex,
                holdEnd, holdRaw⟩).2 hcontinue
          have hprogress : nextIndex.val < state.1.val := by
            rw [holdIndex, hnewIndex]
            omega
          exact Nat.sub_lt_sub_left holdLt hprogress
    · exact ⟨slots, hinvariant⟩
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨result, hcall, hindex, hbase, hxor⟩
  exact ⟨result, hcall, hindex, hbase, hxor⟩

abbrev reduceOne (raw sums : Raw4) (limb : Std.Usize) : Result Raw4 := do
  let word ← Array.index_usize raw limb
  let reduced ← aspis_core.field.M31.reduce_u64 word
  let wide := core.convert.num.FromU64U32.from reduced
  let current ← Array.index_usize sums limb
  Array.update sums limb (Std.U64.wrapping_add current wide)

private theorem reduceOne_spec (natural : LocalNatural) (weights : LocalWeights)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (mask block : Nat) (hmask : MaskBound mask) (raw sums : Raw4)
    (limb : Std.Usize)
    (hinvariant : SingleReduceInvariant natural weights shift mask block raw
      sums limb) (hcontinue : limb.val < 4) :
    ∃ next : Raw4,
      reduceOne raw sums limb = .ok next ∧
      SingleReduceInvariant natural weights shift mask block raw next
        (Std.Usize.wrapping_add limb 1#usize) := by
  rcases hinvariant with ⟨hblock, hlimb4, hraw, hsums⟩
  let limbFin : Fin 4 := ⟨limb.val, hcontinue⟩
  have hrawCall : Array.index_usize raw limb =
      .ok (rawEntry raw limbFin) := raw_index_call raw limb hcontinue
  obtain ⟨reduced, hreduceCall, hreduced⟩ :=
    GoodMatricesCurrent.SourceExtractedField.authentic_reduce_u64_word_spec
      (rawEntry raw limbFin)
  have hrawBound : (rawEntry raw limbFin).val < 2 ^ 64 := by
    rw [hraw]
    exact blockRawAt_lt_u64 natural weights hnatural hweights shift mask
      limb.val block hmask hcontinue hblock
  have hreducedCanonical : reduced.val < P := by
    rw [hreduced]
    exact rawReduceU64_canonical _ hrawBound
  have hreducedValue : reduced.val =
      rawReduceU64 (blockRawAt natural weights shift mask limb.val block) := by
    rw [hreduced, hraw]
  let wideReduced : Std.U64 := core.convert.num.FromU64U32.from reduced
  have hwideReduced : wideReduced.val = reduced.val := by simp [wideReduced]
  have hsumsCall : Array.index_usize sums limb =
      .ok (rawEntry sums limbFin) := raw_index_call sums limb hcontinue
  have hcurrentSum : (rawEntry sums limbFin).val =
      outerPrefix natural weights shift mask limb.val block := by
    rw [hsums]
    simp [limbFin]
  let nextValue := Std.U64.wrapping_add (rawEntry sums limbFin) wideReduced
  have hnextBound : outerPrefix natural weights shift mask limb.val
      (block + 1) < 2 ^ 64 := by
    apply outerPrefix_lt_u64 natural weights hnatural hweights shift mask
      limb.val (block + 1) hmask hcontinue
    omega
  have hnextValue : nextValue.val =
      outerPrefix natural weights shift mask limb.val (block + 1) := by
    unfold nextValue
    rw [u64_wrapping_add_exact]
    · rw [hcurrentSum, hwideReduced, hreducedValue, outerPrefix_succ]
    · rw [hcurrentSum, hwideReduced, hreducedValue, ← outerPrefix_succ]
      exact hnextBound
  let next := sums.set limb nextValue
  have hnextModel (output : Fin 4) : (rawEntry next output).val =
      if output.val < limb.val + 1 then
        outerPrefix natural weights shift mask output.val (block + 1)
      else outerPrefix natural weights shift mask output.val block := by
    by_cases heq : output.val = limb.val
    · have hout : output = limbFin := Fin.ext heq
      subst output
      unfold next
      have hsame : rawEntry (sums.set limb nextValue) limbFin = nextValue := by
        unfold rawEntry
        exact List.getElem_set_self (by
          simp only [List.length_set]
          rw [sums.property]
          exact hcontinue)
      rw [hsame, hnextValue]
      simp [limbFin]
    · unfold next
      rw [rawEntry_set_other sums limb nextValue output (by omega), hsums]
      by_cases hbefore : output.val < limb.val
      · have hbeforeNext : output.val < limb.val + 1 := by omega
        simp [hbefore, hbeforeNext]
      · have hafter : limb.val + 1 ≤ output.val := by omega
        simp [Nat.not_lt.mpr hafter, hbefore]
  have hupdate : Array.update sums limb nextValue = .ok next :=
    raw_update_call sums limb hcontinue nextValue
  let limbNext := Std.Usize.wrapping_add limb 1#usize
  have hlimbNext : limbNext.val = limb.val + 1 := by
    apply usize_wrapping_add_one_val
    have := usize_size_large
    omega
  refine ⟨next, ?_, ?_⟩
  · unfold reduceOne
    rw [hrawCall]
    simp only [Aeneas.Std.bind_tc_ok]
    unfold aspis_core.field.M31.reduce_u64
    rw [hreduceCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hsumsCall]
    simp only [Aeneas.Std.bind_tc_ok]
    change Array.update sums limb nextValue = _
    exact hupdate
  · refine ⟨hblock, ?_, hraw, ?_⟩
    · rw [hlimbNext]
      omega
    · intro output
      rw [hlimbNext]
      exact hnextModel output

private abbrev pairedReduceBody :=
  v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0_loop1.body

private abbrev pairedReduceLoop :=
  v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0_loop1

def PairedReduceInvariant (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask block : Nat) (baseRaw xorRaw baseSums xorSums : Raw4)
    (limb : Std.Usize) : Prop :=
  SingleReduceInvariant natural weights shift 0 block baseRaw baseSums limb ∧
  SingleReduceInvariant natural weights shift mask block xorRaw xorSums limb

private theorem pairedReduceBody_step (natural : LocalNatural)
    (weights : LocalWeights) (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (mask block : Nat) (hmask : MaskBound mask)
    (baseRaw xorRaw baseSums xorSums : Raw4) (limb : Std.Usize)
    (hinvariant : PairedReduceInvariant natural weights shift mask block baseRaw
      xorRaw baseSums xorSums limb) (hcontinue : limb.val < 4) :
    ∃ state : Raw4 × Raw4 × Std.Usize,
      pairedReduceBody baseRaw xorRaw baseSums xorSums limb =
        .ok (.cont state) ∧
      state.2.2.val = limb.val + 1 ∧
      PairedReduceInvariant natural weights shift mask block baseRaw xorRaw
        state.1 state.2.1 state.2.2 := by
  rcases reduceOne_spec natural weights hnatural hweights shift 0 block
      mask_zero_bound baseRaw baseSums limb hinvariant.1 hcontinue with
    ⟨baseNext, hbaseCall, hbaseNext⟩
  rcases reduceOne_spec natural weights hnatural hweights shift mask block hmask
      xorRaw xorSums limb hinvariant.2 hcontinue with
    ⟨xorNext, hxorCall, hxorNext⟩
  let limbNext := Std.Usize.wrapping_add limb 1#usize
  have hlimbNext : limbNext.val = limb.val + 1 := by
    apply usize_wrapping_add_one_val
    have := usize_size_large
    omega
  have hcondition : limb < (Array.to_slice baseRaw).len := by
    apply (UScalar.lt_equiv _ _).2
    simpa using hcontinue
  refine ⟨(baseNext, xorNext, limbNext), ?_, hlimbNext, hbaseNext, hxorNext⟩
  unfold pairedReduceBody
  unfold
    v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0_loop1.body
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [if_pos hcondition]
  have hcombined : (do
      let baseNext' ← reduceOne baseRaw baseSums limb
      let xorNext' ← reduceOne xorRaw xorSums limb
      ok (cont (baseNext', xorNext', limbNext))) =
      (.ok (.cont (baseNext, xorNext, limbNext)) :
        Result (ControlFlow (Raw4 × Raw4 × Std.Usize) (Raw4 × Raw4))) := by
    rw [hbaseCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hxorCall]
    simp only [Aeneas.Std.bind_tc_ok]
  simpa only [reduceOne, Aeneas.Std.lift, Aeneas.Std.bind_assoc_eq] using hcombined

private theorem pairedReduceBody_done (baseRaw xorRaw baseSums xorSums : Raw4)
    (limb : Std.Usize) (hlimb : limb.val = 4) :
    pairedReduceBody baseRaw xorRaw baseSums xorSums limb =
      .ok (.done (baseSums, xorSums)) := by
  have hcondition : ¬ limb < (Array.to_slice baseRaw).len := by
    intro hlt
    have hltNat := (UScalar.lt_equiv _ _).1 hlt
    norm_num at hltNat
    omega
  unfold pairedReduceBody
  unfold
    v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0_loop1.body
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [if_neg hcondition]

private theorem pairedReduceBody_transition_spec (natural : LocalNatural)
    (weights : LocalWeights) (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (mask block : Nat) (hmask : MaskBound mask)
    (baseRaw xorRaw baseSums xorSums : Raw4) (limb : Std.Usize)
    (hinvariant : PairedReduceInvariant natural weights shift mask block baseRaw
      xorRaw baseSums xorSums limb) :
    ∃ flow,
      pairedReduceBody baseRaw xorRaw baseSums xorSums limb = .ok flow ∧
      (match flow with
        | .done result =>
            (∀ output : Fin 4, (rawEntry result.1 output).val =
              outerPrefix natural weights shift 0 output.val (block + 1)) ∧
            ∀ output : Fin 4, (rawEntry result.2 output).val =
              outerPrefix natural weights shift mask output.val (block + 1)
        | .cont next =>
            PairedReduceInvariant natural weights shift mask block baseRaw xorRaw
              next.1 next.2.1 next.2.2 ∧
            4 - next.2.2.val < 4 - limb.val) := by
  by_cases hcontinue : limb.val < 4
  · rcases pairedReduceBody_step natural weights hnatural hweights shift mask
      block hmask baseRaw xorRaw baseSums xorSums limb hinvariant hcontinue with
      ⟨state, hcall, hnext, hstate⟩
    refine ⟨.cont state, hcall, hstate, ?_⟩
    rw [hnext]
    omega
  · have hfinal : limb.val = 4 := by
      have hle := hinvariant.1.2.1
      omega
    have hcall := pairedReduceBody_done baseRaw xorRaw baseSums xorSums limb
      hfinal
    refine ⟨.done (baseSums, xorSums), hcall, ?_, ?_⟩
    · intro output
      rw [hinvariant.1.2.2.2 output, hfinal]
      simp
    · intro output
      rw [hinvariant.2.2.2.2 output, hfinal]
      simp

theorem pairedReduceLoop_spec (natural : LocalNatural) (weights : LocalWeights)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (mask block : Nat) (hmask : MaskBound mask)
    (baseRaw xorRaw baseSums xorSums : Raw4) (limb : Std.Usize)
    (hinvariant : PairedReduceInvariant natural weights shift mask block baseRaw
      xorRaw baseSums xorSums limb) :
    ∃ result : Raw4 × Raw4,
      pairedReduceLoop baseSums xorSums baseRaw xorRaw limb = .ok result ∧
      (∀ output : Fin 4, (rawEntry result.1 output).val =
        outerPrefix natural weights shift 0 output.val (block + 1)) ∧
      ∀ output : Fin 4, (rawEntry result.2 output).val =
        outerPrefix natural weights shift mask output.val (block + 1) := by
  have hspec : Aeneas.Std.WP.spec
      (pairedReduceLoop baseSums xorSums baseRaw xorRaw limb)
      (fun result =>
        (∀ output : Fin 4, (rawEntry result.1 output).val =
          outerPrefix natural weights shift 0 output.val (block + 1)) ∧
        ∀ output : Fin 4, (rawEntry result.2 output).val =
          outerPrefix natural weights shift mask output.val (block + 1)) := by
    unfold pairedReduceLoop
    unfold
      v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0_loop1
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun state => 4 - state.2.2.val)
      (inv := fun state => PairedReduceInvariant natural weights shift mask block
        baseRaw xorRaw state.1 state.2.1 state.2.2)
    · rintro ⟨nextBase, nextXor, nextLimb⟩ hstate
      simp only
      apply Aeneas.Std.WP.exists_imp_spec
      have htransition := pairedReduceBody_transition_spec natural weights
        hnatural hweights shift mask block hmask baseRaw xorRaw nextBase nextXor
        nextLimb hstate
      unfold pairedReduceBody at htransition
      rcases htransition with ⟨flow, hcall, hpost⟩
      exact ⟨flow, hcall, by cases flow <;> exact hpost⟩
    · exact hinvariant
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨result, hcall, hbase, hxor⟩
  exact ⟨result, hcall, hbase, hxor⟩

private abbrev pairedOuterBody :=
  v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0.body

private abbrev pairedOuterLoop :=
  v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0

def PairedOuterInvariant (natural : LocalNatural) (weights : LocalWeights)
    (shift : Fin 12) (mask : Nat) (supportEnd : Std.Usize)
    (baseSums xorSums : Raw4) (index : Std.Usize) : Prop :=
  SingleOuterInvariant natural weights shift 0 supportEnd baseSums index ∧
  SingleOuterInvariant natural weights shift mask supportEnd xorSums index

private theorem pairedOuterBody_step (natural : LocalNatural)
    (weights : LocalWeights) (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (runtimeMask : Std.Usize) (mask : Nat) (supportEnd : Std.Usize)
    (baseSums xorSums : Raw4) (index : Std.Usize)
    (hruntimeMask : runtimeMask.val = mask) (hmask : MaskBound mask)
    (hinvariant : PairedOuterInvariant natural weights shift mask supportEnd
      baseSums xorSums index) (hcontinue : index.val < supportEnd.val) :
    ∃ state : Raw4 × Raw4 × Std.Usize,
      pairedOuterBody natural weights runtimeMask supportEnd baseSums xorSums
        index = .ok (.cont state) ∧
      index.val < state.2.2.val ∧
      PairedOuterInvariant natural weights shift mask supportEnd state.1
        state.2.1 state.2.2 := by
  rcases (outer_index_lt_supportEnd_iff natural weights shift 0 supportEnd
      baseSums index hinvariant.1).1 hcontinue with
    ⟨block, hblock6, hindex, hblockActive, hbaseSums⟩
  rcases (outer_index_lt_supportEnd_iff natural weights shift mask supportEnd
      xorSums index hinvariant.2).1 hcontinue with
    ⟨xorBlock, hxorBlock6, hxorIndex, hxorBlockActive, hxorSums⟩
  have hxorBlock : xorBlock = block := by
    rw [hindex] at hxorIndex
    omega
  subst xorBlock
  have hblock : block < 6 := by
    have hcount := (deployedSupportCount_bounds shift).2
    omega
  have hcondition : index < supportEnd :=
    (UScalar.lt_equiv _ _).2 hcontinue
  let plusEight := Std.Usize.wrapping_add index 8#usize
  have hplusEight : plusEight.val = index.val + 8 := by
    apply usize_wrapping_add_eight_val
    have := usize_size_large
    have hindexBound : index.val < 64 := by
      rw [hindex]
      have hcount := (deployedSupportCount_bounds shift).2
      have hshift := shift.isLt
      omega
    omega
  obtain ⟨blockEnd, hblockEndCall, hblockEnd⟩ :=
    usize_min_spec plusEight supportEnd
  have hsupportEnd : supportEnd.val = deployedSupportEnd shift :=
    hinvariant.1.choose_spec.2.2.1
  have hblockEndValue : blockEnd.val = Nat.min
      (shift.val % 2 + 2 * (4 * block) + 8)
      (deployedSupportEnd shift) := by
    rw [hblockEnd, hplusEight, hindex, hsupportEnd]
  let zeroRaw : Raw4 := Array.repeat 4#usize 0#u64
  have hbaseInner : SingleInnerInvariant natural weights shift 0 block 0 blockEnd
      index zeroRaw := by
    refine ⟨hblock, hblockActive, by norm_num, by omega, hindex,
      hblockEndValue, ?_⟩
    intro limb
    rw [repeated_zero_raw]
    simp [slotPrefix]
  have hxorInner : SingleInnerInvariant natural weights shift mask block 0
      blockEnd index zeroRaw := by
    refine ⟨hblock, hblockActive, by norm_num, by omega, hindex,
      hblockEndValue, ?_⟩
    intro limb
    rw [repeated_zero_raw]
    simp [slotPrefix]
  have hinnerInvariant : PairedInnerInvariant natural weights shift mask block 0
      blockEnd index zeroRaw zeroRaw := ⟨hbaseInner, hxorInner⟩
  rcases pairedInnerLoop_spec natural weights hnatural hweights shift runtimeMask
      mask block 0 blockEnd index zeroRaw zeroRaw hruntimeMask hmask
      hinnerInvariant with
    ⟨inner, hinnerCall, hinnerIndex, hbaseRaw, hxorRaw⟩
  have hbaseReduce : SingleReduceInvariant natural weights shift 0 block
      inner.2.1 baseSums 0#usize := by
    refine ⟨hblock, by norm_num, hbaseRaw, ?_⟩
    intro limb
    rw [hbaseSums]
    simp
  have hxorReduce : SingleReduceInvariant natural weights shift mask block
      inner.2.2 xorSums 0#usize := by
    refine ⟨hblock, by norm_num, hxorRaw, ?_⟩
    intro limb
    rw [hxorSums]
    simp
  have hreduceInvariant : PairedReduceInvariant natural weights shift mask block
      inner.2.1 inner.2.2 baseSums xorSums 0#usize :=
    ⟨hbaseReduce, hxorReduce⟩
  rcases pairedReduceLoop_spec natural weights hnatural hweights shift mask block
      hmask inner.2.1 inner.2.2 baseSums xorSums 0#usize hreduceInvariant with
    ⟨nextSums, hreduceCall, hnextBase, hnextXor⟩
  have hprogress : index.val < inner.1.val := by
    rw [hindex, hinnerIndex]
    unfold blockLogicalEnd
    have hminGrowth : 4 * block <
        Nat.min (4 * (block + 1)) (deployedSupportCount shift) := by
      apply lt_min
      · omega
      · exact hblockActive
    omega
  refine ⟨(nextSums.1, nextSums.2, inner.1), ?_, hprogress, ?_⟩
  · unfold pairedOuterBody
    unfold
      v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0.body
    rw [if_pos hcondition]
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
    change (do
      let block_end ← core.cmp.min core.cmp.OrdUsize plusEight supportEnd
      let innerResult ← pairedInnerLoop natural weights runtimeMask index
        block_end zeroRaw zeroRaw
      let sumsResult ← pairedReduceLoop baseSums xorSums innerResult.2.1
        innerResult.2.2 0#usize
      ok (cont (sumsResult.1, sumsResult.2, innerResult.1))) = _
    rw [hblockEndCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hinnerCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hreduceCall]
    simp only [Aeneas.Std.bind_tc_ok]
  · constructor
    · refine ⟨block + 1, by omega, ?_, hsupportEnd, hnextBase⟩
      rw [hinnerIndex]
      rfl
    · refine ⟨block + 1, by omega, ?_, hsupportEnd, hnextXor⟩
      rw [hinnerIndex]
      rfl

private theorem pairedOuterBody_done (natural : LocalNatural)
    (weights : LocalWeights) (runtimeMask : Std.Usize)
    (supportEnd : Std.Usize) (baseSums xorSums : Raw4) (index : Std.Usize)
    (hstop : ¬ index.val < supportEnd.val) :
    pairedOuterBody natural weights runtimeMask supportEnd baseSums xorSums index =
      .ok (.done (baseSums, xorSums)) := by
  have hcondition : ¬ index < supportEnd := by
    intro hlt
    exact hstop ((UScalar.lt_equiv _ _).1 hlt)
  unfold pairedOuterBody
  unfold
    v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0.body
  rw [if_neg hcondition]

private theorem pairedOuterBody_transition_spec (natural : LocalNatural)
    (weights : LocalWeights) (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (runtimeMask : Std.Usize) (mask : Nat) (supportEnd : Std.Usize)
    (baseSums xorSums : Raw4) (index : Std.Usize)
    (hruntimeMask : runtimeMask.val = mask) (hmask : MaskBound mask)
    (hinvariant : PairedOuterInvariant natural weights shift mask supportEnd
      baseSums xorSums index) :
    ∃ flow,
      pairedOuterBody natural weights runtimeMask supportEnd baseSums xorSums
        index = .ok flow ∧
      (match flow with
        | .done result =>
            (∀ limb : Fin 4, (rawEntry result.1 limb).val =
              outerPrefix natural weights shift 0 limb.val 6) ∧
            ∀ limb : Fin 4, (rawEntry result.2 limb).val =
              outerPrefix natural weights shift mask limb.val 6
        | .cont next =>
            PairedOuterInvariant natural weights shift mask supportEnd next.1
              next.2.1 next.2.2 ∧
            supportEnd.val - next.2.2.val <
              supportEnd.val - index.val) := by
  by_cases hcontinue : index.val < supportEnd.val
  · rcases pairedOuterBody_step natural weights hnatural hweights shift
      runtimeMask mask supportEnd baseSums xorSums index hruntimeMask hmask
      hinvariant hcontinue with ⟨state, hcall, hprogress, hstate⟩
    refine ⟨.cont state, hcall, hstate, ?_⟩
    exact Nat.sub_lt_sub_left hcontinue hprogress
  · have hcall := pairedOuterBody_done natural weights runtimeMask supportEnd
      baseSums xorSums index hcontinue
    rcases hinvariant.1 with ⟨block, hblocks, hindex, hend, hbaseSums⟩
    rcases hinvariant.2 with ⟨xorBlock, hxorBlocks, hxorIndex, hxorEnd,
      hxorSums⟩
    have hfinal : deployedSupportCount shift ≤ 4 * block := by
      by_contra hnot
      have hactive : 4 * block < deployedSupportCount shift := by omega
      have hmin : (4 * block).min (deployedSupportCount shift) = 4 * block :=
        Nat.min_eq_left (Nat.le_of_lt hactive)
      apply hcontinue
      rw [hindex, hmin, hend]
      have hlt := deployedSupportIndex_lt_end shift (4 * block) hactive
      simpa [deployedSupportIndex] using hlt
    have hxorFinal : deployedSupportCount shift ≤ 4 * xorBlock := by
      by_contra hnot
      have hactive : 4 * xorBlock < deployedSupportCount shift := by omega
      have hmin : (4 * xorBlock).min (deployedSupportCount shift) =
          4 * xorBlock := Nat.min_eq_left (Nat.le_of_lt hactive)
      apply hcontinue
      rw [hxorIndex, hmin, hxorEnd]
      have hlt := deployedSupportIndex_lt_end shift (4 * xorBlock) hactive
      simpa [deployedSupportIndex] using hlt
    refine ⟨.done (baseSums, xorSums), hcall, ?_, ?_⟩
    · intro limb
      rw [hbaseSums]
      exact outerPrefix_final natural weights shift 0 limb.val block hblocks
        hfinal
    · intro limb
      rw [hxorSums]
      exact outerPrefix_final natural weights shift mask limb.val xorBlock
        hxorBlocks hxorFinal

theorem pairedOuterLoop_spec (natural : LocalNatural) (weights : LocalWeights)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (shift : Fin 12)
    (runtimeMask : Std.Usize) (mask : Nat) (supportEnd : Std.Usize)
    (baseSums xorSums : Raw4) (index : Std.Usize)
    (hruntimeMask : runtimeMask.val = mask) (hmask : MaskBound mask)
    (hinvariant : PairedOuterInvariant natural weights shift mask supportEnd
      baseSums xorSums index) :
    ∃ result : Raw4 × Raw4,
      pairedOuterLoop natural weights runtimeMask supportEnd baseSums xorSums
        index = .ok result ∧
      (∀ limb : Fin 4, (rawEntry result.1 limb).val =
        outerPrefix natural weights shift 0 limb.val 6) ∧
      ∀ limb : Fin 4, (rawEntry result.2 limb).val =
        outerPrefix natural weights shift mask limb.val 6 := by
  have hspec : Aeneas.Std.WP.spec
      (pairedOuterLoop natural weights runtimeMask supportEnd baseSums xorSums
        index)
      (fun result =>
        (∀ limb : Fin 4, (rawEntry result.1 limb).val =
          outerPrefix natural weights shift 0 limb.val 6) ∧
        ∀ limb : Fin 4, (rawEntry result.2 limb).val =
          outerPrefix natural weights shift mask limb.val 6) := by
    unfold pairedOuterLoop
    unfold
      v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor_loop0
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun state => supportEnd.val - state.2.2.val)
      (inv := fun state => PairedOuterInvariant natural weights shift mask
        supportEnd state.1 state.2.1 state.2.2)
    · rintro ⟨nextBase, nextXor, nextIndex⟩ hstate
      simp only
      apply Aeneas.Std.WP.exists_imp_spec
      have htransition := pairedOuterBody_transition_spec natural weights
        hnatural hweights shift runtimeMask mask supportEnd nextBase nextXor
        nextIndex hruntimeMask hmask hstate
      unfold pairedOuterBody at htransition
      rcases htransition with ⟨flow, hcall, hpost⟩
      exact ⟨flow, hcall, by cases flow <;> exact hpost⟩
    · exact hinvariant
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨result, hcall, hbase, hxor⟩
  exact ⟨result, hcall, hbase, hxor⟩

theorem evaluate_shifted_in_aligned_block_base_xor_exact_spec
    (natural : LocalNatural) (weights : LocalWeights)
    (runtimeShift runtimeMask : Std.Usize) (shift : Fin 12) (mask : Nat)
    (hruntimeShift : runtimeShift.val = shift.val)
    (hruntimeMask : runtimeMask.val = mask)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights weights) (hmask : MaskBound mask) :
    ∃ baseResult xorResult : LocalQM31,
      v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor
        natural runtimeShift weights runtimeMask =
          .ok (Array.make 2#usize [baseResult, xorResult]) ∧
      CanonicalLocalQM31 baseResult ∧
      CanonicalLocalQM31 xorResult ∧
      qm31ToExact baseResult = deployedBatchedQM31 natural weights shift 0 ∧
      qm31ToExact xorResult = deployedBatchedQM31 natural weights shift mask := by
  let degreePlusShift := Std.Usize.wrapping_add
    v5_cu_probe.good_gate_probe.KERNEL_DEGREE runtimeShift
  have hdegreePlusShift : degreePlusShift.val = 36 + shift.val := by
    unfold degreePlusShift
    rw [Std.Usize.wrapping_add_val_eq,
      v5_cu_probe.good_gate_probe.KERNEL_DEGREE, hruntimeShift]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits, hp] at ⊢ <;>
      omega
  let supportEnd := Std.Usize.wrapping_add degreePlusShift 1#usize
  have hsupportEnd : supportEnd.val = deployedSupportEnd shift := by
    unfold supportEnd
    rw [usize_wrapping_add_one_val]
    · rw [hdegreePlusShift]
      unfold deployedSupportEnd
      omega
    · rw [hdegreePlusShift]
      have := usize_size_large
      omega
  let zeroSums : Raw4 := Array.repeat 4#usize 0#u64
  let startIndex := runtimeShift &&& 1#usize
  have hstartIndex : startIndex.val = shift.val % 2 := by
    unfold startIndex
    rw [usize_and_one_val, hruntimeShift]
  have hbaseOuter : SingleOuterInvariant natural weights shift 0 supportEnd
      zeroSums startIndex := by
    refine ⟨0, by norm_num, ?_, hsupportEnd, ?_⟩
    · rw [hstartIndex]
      norm_num
    · intro limb
      rw [repeated_zero_raw]
      simp [outerPrefix]
  have hxorOuter : SingleOuterInvariant natural weights shift mask supportEnd
      zeroSums startIndex := by
    refine ⟨0, by norm_num, ?_, hsupportEnd, ?_⟩
    · rw [hstartIndex]
      norm_num
    · intro limb
      rw [repeated_zero_raw]
      simp [outerPrefix]
  have houterInvariant : PairedOuterInvariant natural weights shift mask
      supportEnd zeroSums zeroSums startIndex := ⟨hbaseOuter, hxorOuter⟩
  rcases pairedOuterLoop_spec natural weights hnatural hweights shift runtimeMask
      mask supportEnd zeroSums zeroSums startIndex hruntimeMask hmask
      houterInvariant with ⟨sums, hloop, hbaseSums, hxorSums⟩
  have baseReduceSpec (limb : Fin 4) : ∃ reduced : LocalM31,
      aspis_core.field.M31.reduce_u64 (rawEntry sums.1 limb) = .ok reduced ∧
      reduced.val < P ∧
      reduced.val = deployedBatchedLimb natural weights shift 0 limb.val := by
    have hbound : (rawEntry sums.1 limb).val < 2 ^ 64 := by
      rw [hbaseSums]
      exact outerPrefix_lt_u64 natural weights hnatural hweights shift 0
        limb.val 6 mask_zero_bound limb.isLt (by norm_num)
    rcases GoodMatricesCurrent.SourceExtractedField.authentic_reduce_u64_word_spec
        (rawEntry sums.1 limb) with ⟨reduced, hcall, hvalue⟩
    refine ⟨reduced, hcall, ?_, ?_⟩
    · rw [hvalue]
      exact rawReduceU64_canonical _ hbound
    · rw [hvalue, hbaseSums, deployedBatchedLimb_eq_reduce_outerPrefix]
  have xorReduceSpec (limb : Fin 4) : ∃ reduced : LocalM31,
      aspis_core.field.M31.reduce_u64 (rawEntry sums.2 limb) = .ok reduced ∧
      reduced.val < P ∧
      reduced.val = deployedBatchedLimb natural weights shift mask limb.val := by
    have hbound : (rawEntry sums.2 limb).val < 2 ^ 64 := by
      rw [hxorSums]
      exact outerPrefix_lt_u64 natural weights hnatural hweights shift mask
        limb.val 6 hmask limb.isLt (by norm_num)
    rcases GoodMatricesCurrent.SourceExtractedField.authentic_reduce_u64_word_spec
        (rawEntry sums.2 limb) with ⟨reduced, hcall, hvalue⟩
    refine ⟨reduced, hcall, ?_, ?_⟩
    · rw [hvalue]
      exact rawReduceU64_canonical _ hbound
    · rw [hvalue, hxorSums, deployedBatchedLimb_eq_reduce_outerPrefix]
  rcases baseReduceSpec 0 with ⟨b0, hb0, hb0Canonical, hb0Value⟩
  rcases baseReduceSpec 1 with ⟨b1, hb1, hb1Canonical, hb1Value⟩
  rcases baseReduceSpec 2 with ⟨b2, hb2, hb2Canonical, hb2Value⟩
  rcases baseReduceSpec 3 with ⟨b3, hb3, hb3Canonical, hb3Value⟩
  rcases xorReduceSpec 0 with ⟨x0, hx0, hx0Canonical, hx0Value⟩
  rcases xorReduceSpec 1 with ⟨x1, hx1, hx1Canonical, hx1Value⟩
  rcases xorReduceSpec 2 with ⟨x2, hx2, hx2Canonical, hx2Value⟩
  rcases xorReduceSpec 3 with ⟨x3, hx3, hx3Canonical, hx3Value⟩
  let baseResult : LocalQM31 :=
    { c0 := { a := b0, b := b1 }, c1 := { a := b2, b := b3 } }
  let xorResult : LocalQM31 :=
    { c0 := { a := x0, b := x1 }, c1 := { a := x2, b := x3 } }
  refine ⟨baseResult, xorResult, ?_, ?_, ?_, ?_, ?_⟩
  · unfold
      v5_cu_probe.good_gate_probe.evaluate_shifted_in_aligned_block_base_xor
    simp only [Aeneas.Std.lift]
    change (do
      let sumsResult ← pairedOuterLoop natural weights runtimeMask supportEnd
        zeroSums zeroSums startIndex
      let i1 ← Array.index_usize sumsResult.1 0#usize
      let m0 ← aspis_core.field.M31.reduce_u64 i1
      let i2 ← Array.index_usize sumsResult.1 1#usize
      let m1 ← aspis_core.field.M31.reduce_u64 i2
      let c0 ← aspis_core.field.CM31.new m0 m1
      let i3 ← Array.index_usize sumsResult.1 2#usize
      let m2 ← aspis_core.field.M31.reduce_u64 i3
      let i4 ← Array.index_usize sumsResult.1 3#usize
      let m3 ← aspis_core.field.M31.reduce_u64 i4
      let c1 ← aspis_core.field.CM31.new m2 m3
      let i5 ← Array.index_usize sumsResult.2 0#usize
      let m4 ← aspis_core.field.M31.reduce_u64 i5
      let i6 ← Array.index_usize sumsResult.2 1#usize
      let m5 ← aspis_core.field.M31.reduce_u64 i6
      let c2 ← aspis_core.field.CM31.new m4 m5
      let i7 ← Array.index_usize sumsResult.2 2#usize
      let m6 ← aspis_core.field.M31.reduce_u64 i7
      let i8 ← Array.index_usize sumsResult.2 3#usize
      let m7 ← aspis_core.field.M31.reduce_u64 i8
      let c3 ← aspis_core.field.CM31.new m6 m7
      ok (Array.make 2#usize
        [({ c0 := c0, c1 } : LocalQM31), ({ c0 := c2, c1 := c3 } : LocalQM31)])) = _
    rw [hloop]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_zero_call sums.1]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hb0]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_one_call sums.1]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hb1]
    simp only [Aeneas.Std.bind_tc_ok]
    unfold aspis_core.field.CM31.new
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_two_call sums.1]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hb2]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_three_call sums.1]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hb3]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_zero_call sums.2]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hx0]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_one_call sums.2]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hx1]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_two_call sums.2]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hx2]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [raw_index_three_call sums.2]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hx3]
    rfl
  · exact ⟨⟨hb0Canonical, hb1Canonical⟩,
      ⟨hb2Canonical, hb3Canonical⟩⟩
  · exact ⟨⟨hx0Canonical, hx1Canonical⟩,
      ⟨hx2Canonical, hx3Canonical⟩⟩
  · unfold baseResult qm31ToExact cm31ToExact deployedBatchedQM31
    rw [hb0Value, hb1Value, hb2Value, hb3Value]
    norm_num
  · unfold xorResult qm31ToExact cm31ToExact deployedBatchedQM31
    rw [hx0Value, hx1Value, hx2Value, hx3Value]
    norm_num

end GoodMatricesCurrent.SourceExtractedTerminalEvaluator
