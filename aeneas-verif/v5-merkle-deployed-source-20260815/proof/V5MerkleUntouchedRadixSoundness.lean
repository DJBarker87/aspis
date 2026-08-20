import V5MerkleUntouchedRadixInversion
import AspisFormal.V5MerkleRustBridge

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000

namespace AspisV5MerkleUntouchedRadixSoundness

open v5_merkle_fixed_hash_adapter
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedRadixInput := Array Std.U8 129#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

def generatedU8ToByte (byte : Std.U8) : ModelByte :=
  ⟨byte.val, by
    have h := UScalar.hBounds byte
    norm_num at h ⊢
    exact h⟩

def generatedArrayToDigest (digest : GeneratedDigest) : Digest32 :=
  fun index => generatedU8ToByte (digest.val.get ⟨index.val, by
    have hlength := digest.property
    change digest.val.length = 32 at hlength
    omega⟩)

theorem digestBytes_generatedArrayToDigest (digest : GeneratedDigest) :
    digestBytes (generatedArrayToDigest digest) =
      digest.val.map generatedU8ToByte := by
  unfold digestBytes generatedArrayToDigest
  simpa using List.ofFn_getElem_eq_map digest.val generatedU8ToByte

/-- The sole executable hash premise: the opaque extraction boundary for
Solana's `hashv` returns SHA-256 of the concatenation of the supplied slices.
This premise says nothing about collision resistance. -/
def FixedHashvEqualsSha256
    (sha256 : List ModelByte → Digest32) : Prop :=
  ∀ inputs output, merkle.fixed_hashv inputs = .ok output →
    generatedArrayToDigest output =
      sha256 ((inputs.val.flatMap fun input => input.val).map generatedU8ToByte)

private theorem generated_u8_ne_spec (left right : Std.U8) :
    liftFun2 core.cmp.impls.PartialEqU8.ne left right =
      .ok (decide (left ≠ right)) := by
  simp [core.cmp.impls.PartialEqU8.ne]

private theorem allM_zip_no_generated_u8_difference
    (left right : List Std.U8) (sameLength : left.length = right.length) :
    List.allM
        (fun pair => do
          let differs ← core.cmp.PartialEqU8.ne pair.1 pair.2
          ok (decide (¬ differs = true)))
        (List.zip left right) = .ok true →
      left = right := by
  induction left generalizing right with
  | nil =>
      intro hrun
      cases right <;> simp_all
  | cons head tail ih =>
      cases right with
      | nil => simp at sameLength
      | cons head' tail' =>
          intro hrun
          simp only [List.length_cons, Nat.add_right_cancel_iff] at sameLength
          simp only [List.zip_cons_cons, List.allM] at hrun
          generalize htail : List.allM
              (fun pair => do
                let differs ← core.cmp.PartialEqU8.ne pair.1 pair.2
                ok (decide (¬ differs = true)))
              (List.zip tail tail') = tailResult at hrun
          rw [generated_u8_ne_spec head head'] at hrun
          by_cases hHead : head = head'
          · subst head'
            simp [pure] at hrun
            have hTail := ih tail' sameLength (hrun ▸ htail)
            subst tail'
            rfl
          · simp [hHead, pure] at hrun

theorem generated_digest_eq_true_implies_eq (left right : GeneratedDigest)
    (hrun : core.array.equality.PartialEqArray.eq
      core.cmp.PartialEqU8 left right = .ok true) :
    left = right := by
  unfold core.array.equality.PartialEqArray.eq at hrun
  have sameLength : left.length = right.length := by simp
  simp only [sameLength, ↓reduceIte] at hrun
  apply Subtype.ext
  exact allM_zip_no_generated_u8_difference left.val right.val
    (by simpa using sameLength) hrun

theorem fixed_node_hash_exact
    (sha256 : List ModelByte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (left right output : GeneratedDigest)
    (hrun : merkle.fixed_node_hash left right = .ok output) :
    generatedArrayToDigest output =
      sha256 ([0x11] ++ digestBytes (generatedArrayToDigest left) ++
        digestBytes (generatedArrayToDigest right)) := by
  have hleft := left.property
  have hright := right.property
  change left.val.length = 32 at hleft
  change right.val.length = 32 at hright
  have htakeLeft : List.take 32 (left.val.map generatedU8ToByte) =
      left.val.map generatedU8ToByte := by
    apply List.take_of_length_le
    simp [hleft]
  have htakeRight : List.take 32 (right.val.map generatedU8ToByte) =
      right.val.map generatedU8ToByte := by
    apply List.take_of_length_le
    simp [hright]
  unfold merkle.fixed_node_hash at hrun
  simp [Std.lift, Array.update, core.array.Array.index_mut,
    core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    Array.index_usize, Array.make, Slice.len, Slice.length,
    merkle.DOM_NODE, hleft, hright] at hrun
  simp_lists at hrun
  simp at hrun
  have hexact := hhash _ output hrun
  rw [digestBytes_generatedArrayToDigest,
    digestBytes_generatedArrayToDigest]
  simp [List.setSlice!, hleft, hright] at hexact
  rw [htakeLeft, htakeRight] at hexact
  simpa [Array.make, Array.val_to_slice, generatedU8ToByte,
    merkle.DOM_NODE] using hexact

theorem fixed_node_hash_and_compare_exact
    (sha256 : List ModelByte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (left right top root : GeneratedDigest)
    (hnode : merkle.fixed_node_hash left right = .ok top)
    (hcompare : core.array.equality.PartialEqArray.eq
      core.cmp.PartialEqU8 top root = .ok true) :
    (sha256MerkleHashing sha256).binaryNode
        (generatedArrayToDigest left) (generatedArrayToDigest right) =
      generatedArrayToDigest root := by
  have htop := fixed_node_hash_exact sha256 hhash left right top hnode
  have heq := generated_digest_eq_true_implies_eq top root hcompare
  subst root
  exact htop.symm

def generatedDigestBytes (digest : GeneratedDigest) : List Std.U8 :=
  digest.val

def rawRadixPreimage (children : Fin 4 → GeneratedDigest) : List Std.U8 :=
  [merkle.DOM_NODE4] ++ (generatedDigestBytes (children 0) ++
    (generatedDigestBytes (children 1) ++
      (generatedDigestBytes (children 2) ++
        generatedDigestBytes (children 3))))

theorem rawRadixPreimage_length (children : Fin 4 → GeneratedDigest) :
    (rawRadixPreimage children).length = 129 := by
  simp [rawRadixPreimage, generatedDigestBytes]

theorem raw_radix_hash_exact
    (sha256 : List ModelByte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (children : Fin 4 → GeneratedDigest)
    (input : GeneratedRadixInput) (output : GeneratedDigest)
    (hinput : input.val = rawRadixPreimage children)
    (hrun : merkle.fixed_hashv
      (Array.to_slice (Array.make 1#usize [Array.to_slice input] (by rfl))) =
        .ok output) :
    generatedArrayToDigest output =
      (sha256MerkleHashing sha256).radix4Node
        (fun slot => generatedArrayToDigest (children slot)) := by
  have hexact := hhash _ output hrun
  simp only [sha256MerkleHashing, hashInputBytes]
  rw [digestBytes_generatedArrayToDigest,
    digestBytes_generatedArrayToDigest,
    digestBytes_generatedArrayToDigest,
    digestBytes_generatedArrayToDigest]
  simpa [Array.make, Array.val_to_slice, rawRadixPreimage,
    generatedDigestBytes, generatedU8ToByte, hinput,
    merkle.DOM_NODE4] using hexact

private theorem slot_start_val (slot : Std.Usize) (hslot : slot.val < 4) :
    (Std.Usize.wrapping_add 1#usize
      (Std.Usize.wrapping_mul slot 32#usize)).val =
        1 + slot.val * 32 := by
  have hsizes : UScalar.size .Usize = Usize.size :=
    UScalar.size_UScalarTyUsize
  have hsize : 130 < UScalar.size .Usize := by
    have h := (130#usize).hSize
    simpa using h
  have hmul : (Std.Usize.wrapping_mul slot 32#usize).val =
      slot.val * 32 := by
    rw [Std.Usize.wrapping_mul_val_eq]
    norm_num
    apply Nat.mod_eq_of_lt
    rw [← hsizes]
    omega
  rw [Std.Usize.wrapping_add_val_eq, hmul]
  norm_num
  apply Nat.mod_eq_of_lt
  rw [← hsizes]
  omega

private theorem slot_end_val (slot : Std.Usize) (hslot : slot.val < 4) :
    (Std.Usize.wrapping_add 1#usize
      (Std.Usize.wrapping_mul
        (Std.Usize.wrapping_add slot 1#usize) 32#usize)).val =
        1 + (slot.val + 1) * 32 := by
  have hsize : 130 < UScalar.size .Usize := by
    have h := (130#usize).hSize
    simpa using h
  have hsizes : UScalar.size .Usize = Usize.size :=
    UScalar.size_UScalarTyUsize
  have hsucc : (Std.Usize.wrapping_add slot 1#usize).val =
      slot.val + 1 := by
    rw [Std.Usize.wrapping_add_val_eq]
    norm_num
    apply Nat.mod_eq_of_lt
    rw [← hsizes]
    omega
  have hmul : (Std.Usize.wrapping_mul
      (Std.Usize.wrapping_add slot 1#usize) 32#usize).val =
      (slot.val + 1) * 32 := by
    rw [Std.Usize.wrapping_mul_val_eq, hsucc]
    norm_num
    apply Nat.mod_eq_of_lt
    rw [← hsizes]
    omega
  rw [Std.Usize.wrapping_add_val_eq, hmul]
  norm_num
  apply Nat.mod_eq_of_lt
  rw [← hsizes]
  omega

private theorem usize_succ_val (value : Std.Usize)
    (hroom : value.val + 1 < UScalar.size .Usize) :
    (Std.Usize.wrapping_add value 1#usize).val = value.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  apply Nat.mod_eq_of_lt
  simpa only [UScalar.size_UScalarTyUsize] using hroom

private theorem usize_add_32_val (value : Std.Usize)
    (hroom : value.val + 32 < UScalar.size .Usize) :
    (Std.Usize.wrapping_add value 32#usize).val = value.val + 32 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  apply Nat.mod_eq_of_lt
  simpa only [UScalar.size_UScalarTyUsize] using hroom

/-- The exact direct slice write performed by one iteration of the unchanged
inner loop. -/
noncomputable def rawWriteChildSlice
    (input : GeneratedRadixInput) (slot : Std.Usize)
    (source : Slice Std.U8) : Result GeneratedRadixInput := do
  let start := Std.Usize.wrapping_add 1#usize
    (Std.Usize.wrapping_mul slot 32#usize)
  let nextSlot := Std.Usize.wrapping_add slot 1#usize
  let stop := Std.Usize.wrapping_add 1#usize
    (Std.Usize.wrapping_mul nextSlot 32#usize)
  let (child, back) ← core.array.Array.index_mut
    (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) input
      { start := start, «end» := stop }
  let copied ← core.slice.Slice.copy_from_slice
    core.marker.CopyU8 child source
  ok (back copied)

theorem rawWriteChildSlice_exact
    (input output : GeneratedRadixInput) (slot : Std.Usize)
    (source : Slice Std.U8)
    (hslot : slot.val < 4) (hsource : source.val.length = 32)
    (hrun : rawWriteChildSlice input slot source = .ok output) :
    output = Array.setSlice! input (1 + slot.val * 32) source.val := by
  unfold rawWriteChildSlice at hrun
  have hstart := slot_start_val slot hslot
  have hstop := slot_end_val slot hslot
  have hbound : 1 + (slot.val + 1) * 32 ≤ 129 := by omega
  let start := Std.Usize.wrapping_add 1#usize
    (Std.Usize.wrapping_mul slot 32#usize)
  let stop := Std.Usize.wrapping_add 1#usize
    (Std.Usize.wrapping_mul (Std.Usize.wrapping_add slot 1#usize) 32#usize)
  have hstartStop : start ≤ stop := by
    change start.val ≤ stop.val
    simp only [start, stop, hstart, hstop]
    omega
  have hstopBound : stop ≤ 129#usize := by
    change stop.val ≤ 129
    simp only [stop, hstop]
    exact hbound
  obtain ⟨⟨child, back⟩, hindex, _hchildVal, hchildLength, hback⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Array.index_mut_SliceIndexRangeUsizeSlice.step input
        { start := start, «end» := stop } hstartStop hstopBound)
  dsimp only at hrun
  rw [hindex] at hrun
  simp only [Aeneas.Std.bind_tc_ok] at hrun
  have hchildLength32 : child.val.length = 32 := by
    change child.val.length = stop.val - start.val at hchildLength
    rw [hstart, hstop] at hchildLength
    omega
  have hcopy : core.slice.Slice.copy_from_slice core.marker.CopyU8
      child source = .ok source := by
    simp [core.slice.Slice.copy_from_slice, Slice.len, Slice.length,
      hchildLength32, hsource]
  rw [hcopy] at hrun
  simp only [Aeneas.Std.bind_tc_ok] at hrun
  have hout : back source = output := Result.ok.inj hrun
  apply Subtype.ext
  rw [← hout, hback source]
  simp only [Array.setSlice!]
  simp only [start, hstart]

theorem rawWriteChildSlice_tag
    (input output : GeneratedRadixInput) (slot : Std.Usize)
    (source : Slice Std.U8)
    (hslot : slot.val < 4) (hsource : source.val.length = 32)
    (hrun : rawWriteChildSlice input slot source = .ok output) :
    output.val[0]! = input.val[0]! := by
  rw [rawWriteChildSlice_exact input output slot source hslot hsource hrun]
  rw [← Array.getElem!_Nat_eq
      (Array.setSlice! input (1 + slot.val * 32) source.val) 0,
    ← Array.getElem!_Nat_eq input 0]
  exact Array.setSlice!_getElem!_prefix input source.val
    (1 + slot.val * 32) 0 (by omega)

theorem rawWriteChildSlice_current
    (input output : GeneratedRadixInput) (slot : Std.Usize)
    (source : Slice Std.U8)
    (hslot : slot.val < 4) (hsource : source.val.length = 32)
    (hrun : rawWriteChildSlice input slot source = .ok output) :
    ∀ byte, byte < 32 →
      output.val[1 + slot.val * 32 + byte]! = source.val[byte]! := by
  intro byte hbyte
  rw [rawWriteChildSlice_exact input output slot source hslot hsource hrun]
  rw [← Array.getElem!_Nat_eq
      (Array.setSlice! input (1 + slot.val * 32) source.val)
      (1 + slot.val * 32 + byte)]
  have hmiddle := Array.setSlice!_getElem!_middle input source.val
    (1 + slot.val * 32) (1 + slot.val * 32 + byte) (by
      constructor
      · omega
      constructor
      · rw [hsource]
        omega
      · simp only [Array.length_eq]
        norm_num
        omega)
  simpa using hmiddle

theorem rawWriteChildSlice_previous
    (input output : GeneratedRadixInput) (slot : Std.Usize)
    (source : Slice Std.U8)
    (hslot : slot.val < 4) (hsource : source.val.length = 32)
    (hrun : rawWriteChildSlice input slot source = .ok output) :
    ∀ earlier, earlier < slot.val → ∀ byte, byte < 32 →
      output.val[1 + earlier * 32 + byte]! =
        input.val[1 + earlier * 32 + byte]! := by
  intro earlier hearlier byte hbyte
  rw [rawWriteChildSlice_exact input output slot source hslot hsource hrun]
  rw [← Array.getElem!_Nat_eq
      (Array.setSlice! input (1 + slot.val * 32) source.val)
      (1 + earlier * 32 + byte),
    ← Array.getElem!_Nat_eq input (1 + earlier * 32 + byte)]
  exact Array.setSlice!_getElem!_prefix input source.val
    (1 + slot.val * 32) (1 + earlier * 32 + byte) (by omega)

/-- Ordered source reads made by the unchanged four-slot loop.  A live bit
advances only the level cursor.  An absent bit consumes exactly the next
32-byte frontier chunk and advances only the frontier cursor. -/
inductive OrderedChildReads
    (nodeBytes : Slice Std.U8) (level : GeneratedDigestVec)
    (present : Std.U8) :
    Nat → Std.Usize → Std.Usize → List GeneratedDigest →
      Std.Usize → Std.Usize → Prop
  | nil (nodePos valuePos : Std.Usize) :
      OrderedChildReads nodeBytes level present 0 nodePos valuePos []
        nodePos valuePos
  | live {count : Nat} {startNodePos startValuePos nodePos valuePos : Std.Usize}
      {children : List GeneratedDigest} (slot : Std.Usize)
      (child : GeneratedDigest) (nextValuePos : Std.Usize)
      (prior : OrderedChildReads nodeBytes level present count
        startNodePos startValuePos children nodePos valuePos)
      (slot_eq : slot.val = count) (slot_lt : count < 4)
      (present_bit :
        present &&& Std.U8.wrapping_shl 1#u8 (UScalar.cast .U32 slot) != 0#u8)
      (value_bound : valuePos.val < level.val.length)
      (child_eq : child = level.val[valuePos.val]!)
      (next_value_eq : nextValuePos.val = valuePos.val + 1) :
      OrderedChildReads nodeBytes level present (count + 1)
        startNodePos startValuePos (children ++ [child]) nodePos nextValuePos
  | frontier {count : Nat}
      {startNodePos startValuePos nodePos valuePos : Std.Usize}
      {children : List GeneratedDigest} (slot : Std.Usize)
      (child : GeneratedDigest) (nextNodePos : Std.Usize)
      (prior : OrderedChildReads nodeBytes level present count
        startNodePos startValuePos children nodePos valuePos)
      (slot_eq : slot.val = count) (slot_lt : count < 4)
      (absent_bit : ¬
        (present &&& Std.U8.wrapping_shl 1#u8 (UScalar.cast .U32 slot) != 0#u8))
      (frontier_room : nodePos.val + 32 ≤ nodeBytes.val.length)
      (child_bytes : ∀ byte, byte < 32 →
        child.val[byte]! = nodeBytes.val[nodePos.val + byte]!)
      (next_node_eq : nextNodePos.val = nodePos.val + 32) :
      OrderedChildReads nodeBytes level present (count + 1)
        startNodePos startValuePos (children ++ [child]) nextNodePos valuePos

theorem OrderedChildReads.finalNodePos_le
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    {present : Std.U8} {count : Nat}
    {startNodePos startValuePos finalNodePos finalValuePos : Std.Usize}
    {children : List GeneratedDigest}
    (reads : OrderedChildReads nodeBytes level present count startNodePos
      startValuePos children finalNodePos finalValuePos)
    (hstart : startNodePos.val ≤ nodeBytes.val.length) :
    finalNodePos.val ≤ nodeBytes.val.length := by
  induction reads with
  | nil => exact hstart
  | live _ _ _ _ _ _ _ _ _ _ ih => exact ih hstart
  | frontier _ _ _ _ _ _ _ room _ next_eq _ =>
      rw [next_eq]
      exact room

def FilledChildPrefix (input : GeneratedRadixInput)
    (children : List GeneratedDigest) : Prop :=
  input.val[0]! = merkle.DOM_NODE4 ∧
    ∀ slot, slot < children.length → ∀ byte, byte < 32 →
      input.val[1 + slot * 32 + byte]! = children[slot]!.val[byte]!

theorem filledChildPrefix_append
    (input output : GeneratedRadixInput) (slot : Std.Usize)
    (source : Slice Std.U8) (children : List GeneratedDigest)
    (child : GeneratedDigest)
    (hslot : slot.val = children.length) (hslotBound : slot.val < 4)
    (hsource : source.val.length = 32) (hchild : child.val = source.val)
    (hprefix : FilledChildPrefix input children)
    (hwrite : rawWriteChildSlice input slot source = .ok output) :
    FilledChildPrefix output (children ++ [child]) := by
  constructor
  · exact (rawWriteChildSlice_tag input output slot source hslotBound
      hsource hwrite).trans hprefix.1
  · intro target htarget byte hbyte
    simp only [List.length_append, List.length_singleton] at htarget
    by_cases hearlier : target < children.length
    · have hpreserved := rawWriteChildSlice_previous input output slot
        source hslotBound hsource hwrite target (by omega) byte hbyte
      rw [hpreserved, List.getElem!_append_left children [child] target
        hearlier]
      exact hprefix.2 target hearlier byte hbyte
    · have htargetEq : target = children.length := by omega
      subst target
      have hcurrent := rawWriteChildSlice_current input output slot source
        hslotBound hsource hwrite byte hbyte
      rw [hslot] at hcurrent
      rw [hcurrent, List.getElem!_append_right children [child]
        children.length (by simp)]
      simp only [Nat.sub_self, List.getElem!_cons_zero]
      rw [hchild]

def childrenOfFour (children : List GeneratedDigest)
    (_hlen : children.length = 4) : Fin 4 → GeneratedDigest :=
  fun slot => children[slot.val]!

theorem input_eq_rawRadixPreimage_of_filled_four
    (input : GeneratedRadixInput) (children : List GeneratedDigest)
    (hlen : children.length = 4)
    (hfilled : FilledChildPrefix input children) :
    input.val = rawRadixPreimage (childrenOfFour children hlen) := by
  let child : Fin 4 → GeneratedDigest := childrenOfFour children hlen
  unfold rawRadixPreimage generatedDigestBytes childrenOfFour
  have hchild0 : child 0 = children[(0 : Fin 4).val]! := rfl
  have hchild1 : child 1 = children[(1 : Fin 4).val]! := rfl
  have hchild2 : child 2 = children[(2 : Fin 4).val]! := rfl
  have hchild3 : child 3 = children[(3 : Fin 4).val]! := rfl
  rw [← hchild0, ← hchild1, ← hchild2, ← hchild3]
  apply List.ext_getElem
  · simp [input.property, (child 0).property, (child 1).property,
      (child 2).property, (child 3).property]
  · intro index hleft hright
    rw [List.Inhabited_getElem_eq_getElem! input.val index hleft,
      List.Inhabited_getElem_eq_getElem! _ index hright]
    by_cases hzero : index = 0
    · subst index
      simpa using hfilled.1
    by_cases hslot0 : index < 33
    · have hbyte : index - 1 < 32 := by omega
      have hslot := hfilled.2 0 (by rw [hlen]; omega) (index - 1) hbyte
      have hrhs :
          ([merkle.DOM_NODE4] ++ ((child 0).val ++
            ((child 1).val ++ ((child 2).val ++
              (child 3).val))))[index]! =
              (child 0).val[index - 1]! := by
        rw [List.getElem!_append_right
          [merkle.DOM_NODE4]
          ((child 0).val ++ ((child 1).val ++
            ((child 2).val ++ (child 3).val)))
          index (by simp; omega)]
        change ((child 0).val ++ ((child 1).val ++
          ((child 2).val ++ (child 3).val)))[index - 1]! = _
        rw [List.getElem!_append_left
          (child 0).val
          ((child 1).val ++ ((child 2).val ++ (child 3).val))
          (index - 1) (by simpa [(child 0).property] using hbyte)]
      rw [hrhs]
      change input.val[index]! = (child 0).val[index - 1]!
      change input.val[1 + 0 * 32 + (index - 1)]! =
        (child 0).val[index - 1]! at hslot
      rw [show 1 + 0 * 32 + (index - 1) = index by omega] at hslot
      exact hslot
    by_cases hslot1 : index < 65
    · have hbyte : index - 33 < 32 := by omega
      have hslot := hfilled.2 1 (by rw [hlen]; omega) (index - 33) hbyte
      have hrhs :
          ([merkle.DOM_NODE4] ++ ((child 0).val ++
            ((child 1).val ++ ((child 2).val ++
              (child 3).val))))[index]! =
              (child 1).val[index - 33]! := by
        rw [List.getElem!_append_right
          [merkle.DOM_NODE4]
          ((child 0).val ++ ((child 1).val ++
            ((child 2).val ++ (child 3).val)))
          index (by simp; omega)]
        change ((child 0).val ++ ((child 1).val ++
          ((child 2).val ++ (child 3).val)))[index - 1]! = _
        rw [List.getElem!_append_right
          (child 0).val
          ((child 1).val ++ ((child 2).val ++ (child 3).val))
          (index - 1) (by simp [(child 0).property]; omega)]
        have hoff0 : index - 1 - (child 0).val.length =
            index - 33 := by
          have hlen0 : (child 0).val.length = 32 := by
            simpa using (child 0).property
          rw [hlen0]
          omega
        rw [hoff0]
        rw [List.getElem!_append_left
          (child 1).val
          ((child 2).val ++ (child 3).val) (index - 33)
          (by simpa [(child 1).property] using hbyte)]
      rw [hrhs]
      change input.val[index]! = (child 1).val[index - 33]!
      change input.val[1 + 1 * 32 + (index - 33)]! =
        (child 1).val[index - 33]! at hslot
      rw [show 1 + 1 * 32 + (index - 33) = index by omega] at hslot
      exact hslot
    by_cases hslot2 : index < 97
    · have hbyte : index - 65 < 32 := by omega
      have hslot := hfilled.2 2 (by rw [hlen]; omega) (index - 65) hbyte
      have hrhs :
          ([merkle.DOM_NODE4] ++ ((child 0).val ++
            ((child 1).val ++ ((child 2).val ++
              (child 3).val))))[index]! =
              (child 2).val[index - 65]! := by
        rw [List.getElem!_append_right
          [merkle.DOM_NODE4]
          ((child 0).val ++ ((child 1).val ++
            ((child 2).val ++ (child 3).val)))
          index (by simp; omega)]
        change ((child 0).val ++ ((child 1).val ++
          ((child 2).val ++ (child 3).val)))[index - 1]! = _
        rw [List.getElem!_append_right
          (child 0).val
          ((child 1).val ++ ((child 2).val ++ (child 3).val))
          (index - 1) (by simp [(child 0).property]; omega)]
        have hoff0 : index - 1 - (child 0).val.length =
            index - 33 := by
          have hlen0 : (child 0).val.length = 32 := by
            simpa using (child 0).property
          rw [hlen0]
          omega
        rw [hoff0]
        rw [List.getElem!_append_right
          (child 1).val ((child 2).val ++ (child 3).val)
          (index - 33) (by simp [(child 1).property]; omega)]
        have hoff1 : index - 33 - (child 1).val.length =
            index - 65 := by
          have hlen1 : (child 1).val.length = 32 := by
            simpa using (child 1).property
          rw [hlen1]
          omega
        rw [hoff1]
        rw [List.getElem!_append_left
          (child 2).val (child 3).val
          (index - 65) (by simpa [(child 2).property] using hbyte)]
      rw [hrhs]
      change input.val[index]! = (child 2).val[index - 65]!
      change input.val[1 + 2 * 32 + (index - 65)]! =
        (child 2).val[index - 65]! at hslot
      rw [show 1 + 2 * 32 + (index - 65) = index by omega] at hslot
      exact hslot
    · have hbyte : index - 97 < 32 := by
        have hlen : input.val.length = 129 := by simpa using input.property
        omega
      have hslot := hfilled.2 3 (by rw [hlen]; omega) (index - 97) hbyte
      have hrhs :
          ([merkle.DOM_NODE4] ++ ((child 0).val ++
            ((child 1).val ++ ((child 2).val ++
              (child 3).val))))[index]! =
              (child 3).val[index - 97]! := by
        rw [List.getElem!_append_right
          [merkle.DOM_NODE4]
          ((child 0).val ++ ((child 1).val ++
            ((child 2).val ++ (child 3).val)))
          index (by simp; omega)]
        change ((child 0).val ++ ((child 1).val ++
          ((child 2).val ++ (child 3).val)))[index - 1]! = _
        rw [List.getElem!_append_right
          (child 0).val
          ((child 1).val ++ ((child 2).val ++ (child 3).val))
          (index - 1) (by simp [(child 0).property]; omega)]
        have hoff0 : index - 1 - (child 0).val.length =
            index - 33 := by
          have hlen0 : (child 0).val.length = 32 := by
            simpa using (child 0).property
          rw [hlen0]
          omega
        rw [hoff0]
        rw [List.getElem!_append_right
          (child 1).val ((child 2).val ++ (child 3).val)
          (index - 33) (by simp [(child 1).property]; omega)]
        have hoff1 : index - 33 - (child 1).val.length =
            index - 65 := by
          have hlen1 : (child 1).val.length = 32 := by
            simpa using (child 1).property
          rw [hlen1]
          omega
        rw [hoff1]
        rw [List.getElem!_append_right
          (child 2).val (child 3).val
          (index - 65) (by simp [(child 2).property]; omega)]
        have hoff2 : index - 65 - (child 2).val.length =
            index - 97 := by
          have hlen2 : (child 2).val.length = 32 := by
            simpa using (child 2).property
          rw [hlen2]
          omega
        rw [hoff2]
      rw [hrhs]
      change input.val[index]! = (child 3).val[index - 97]!
      change input.val[1 + 3 * 32 + (index - 97)]! =
        (child 3).val[index - 97]! at hslot
      rw [show 1 + 3 * 32 + (index - 97) = index by omega] at hslot
      exact hslot

/-- Exact successful result of the unchanged four-slot generated loop.  The
witness records the ordered sources, both cursor effects, the literal
129-byte preimage, the opaque hash call, and the append to the next level. -/
structure RawChildHashWitness
    (sha256 : List ModelByte → Digest32)
    (nodeBytes : Slice Std.U8) (level : GeneratedDigestVec)
    (present : Std.U8) (startNodePos startValuePos : Std.Usize)
    (next finalNext : GeneratedDigestVec)
    (finalNodePos finalValuePos : Std.Usize) where
  children : List GeneratedDigest
  children_length : children.length = 4
  finalInput : GeneratedRadixInput
  digest : GeneratedDigest
  ordered_reads : OrderedChildReads nodeBytes level present 4
    startNodePos startValuePos children finalNodePos finalValuePos
  filled : FilledChildPrefix finalInput children
  preimage_exact :
    finalInput.val = rawRadixPreimage
      (childrenOfFour children children_length)
  hash_run : merkle.fixed_hashv
      (Array.to_slice
        (Array.make 1#usize [Array.to_slice finalInput] (by rfl))) =
    .ok digest
  push_run : alloc.vec.Vec.push next digest = .ok finalNext
  digest_exact : generatedArrayToDigest digest =
    (sha256MerkleHashing sha256).radix4Node
      (fun slot => generatedArrayToDigest
        (childrenOfFour children children_length slot))

private theorem empty_filled_child_prefix
    (input : GeneratedRadixInput)
    (htag : input.val[0]! = merkle.DOM_NODE4) :
    FilledChildPrefix input [] := by
  constructor
  · exact htag
  · simp

private theorem raw_child_loop_from_prefix
    (sha256 : List ModelByte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (remaining : Nat) (iter : core.ops.range.Range Std.Usize)
    (nodeBytes : Slice Std.U8) (level next finalNext : GeneratedDigestVec)
    (present : Std.U8) (pending finalPending : Option Bool)
    (startNodePos startValuePos nodePos valuePos finalNodePos finalValuePos :
      Std.Usize)
    (hstartNode : startNodePos.val ≤ nodeBytes.val.length)
    (hroom : nodeBytes.val.length + 32 < UScalar.size .Usize)
    (input : GeneratedRadixInput) (children : List GeneratedDigest)
    (hspan : iter.start.val + remaining = iter.end.val)
    (hend : iter.end.val = 4)
    (hchildren : children.length = iter.start.val)
    (hreads : OrderedChildReads nodeBytes level present children.length
      startNodePos startValuePos children nodePos valuePos)
    (hfilled : FilledChildPrefix input children)
    (hnodeLe : nodePos.val ≤ nodeBytes.val.length)
    (hrun :
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
        iter nodeBytes level next nodePos valuePos present input pending =
      .ok (finalNext, finalNodePos, finalValuePos, finalPending, 1#u32)) :
    finalPending = pending ∧
      Nonempty (RawChildHashWitness sha256 nodeBytes level present
        startNodePos startValuePos next finalNext finalNodePos finalValuePos) := by
  induction remaining generalizing iter nodePos valuePos input children with
  | zero =>
      have hge : iter.start.val ≥ iter.end.val := by omega
      have hs := core.iter.range.IteratorRange.next_Usize_none_spec iter hge
      rcases Aeneas.Std.WP.spec_imp_exists hs with
        ⟨⟨option, iter'⟩, hnext, hoption, hiter⟩
      rw [hoption, hiter] at hnext
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
        at hrun
      rw [Aeneas.Std.loop.eq_def] at hrun
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0.body
        at hrun
      simp only [hnext, Aeneas.Std.bind_tc_ok, lift] at hrun
      generalize hhashRun : merkle.fixed_hashv
          (Array.to_slice
            (Array.make 1#usize [Array.to_slice input] (by rfl))) =
        hashResult at hrun
      cases hashResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok digest =>
          simp only [Aeneas.Std.bind_tc_ok] at hrun
          generalize hpush : alloc.vec.Vec.push next digest = pushResult at hrun
          cases pushResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok next' =>
              simp only [Aeneas.Std.bind_tc_ok] at hrun
              have hout := Result.ok.inj hrun
              have hnextOut : next' = finalNext :=
                congrArg (fun output => output.1) hout
              have hnodeOut : nodePos = finalNodePos :=
                congrArg (fun output => output.2.1) hout
              have hvalueOut : valuePos = finalValuePos :=
                congrArg (fun output => output.2.2.1) hout
              have hpendingOut : pending = finalPending :=
                congrArg (fun output => output.2.2.2.1) hout
              subst finalNext
              subst finalNodePos
              subst finalValuePos
              subst finalPending
              have hlen : children.length = 4 := by omega
              let hpreimage := input_eq_rawRadixPreimage_of_filled_four
                input children hlen hfilled
              refine ⟨rfl, ⟨{
                children := children
                children_length := hlen
                finalInput := input
                digest := digest
                ordered_reads := ?_
                filled := hfilled
                preimage_exact := hpreimage
                hash_run := hhashRun
                push_run := hpush
                digest_exact := raw_radix_hash_exact sha256 hhash
                  (childrenOfFour children hlen) input digest hpreimage
                  hhashRun }⟩⟩
              simpa [hlen] using hreads
  | succ remaining ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hs := core.iter.range.IteratorRange.next_Usize_some_spec iter hlt
      rcases Aeneas.Std.WP.spec_imp_exists hs with
        ⟨⟨option, iter'⟩, hnext, hoption, hiterStart, hiterEnd⟩
      rw [hoption] at hnext
      have hslot : iter.start.val < 4 := by omega
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
        at hrun
      rw [Aeneas.Std.loop.eq_def] at hrun
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0.body
        at hrun
      simp only [hnext, Aeneas.Std.bind_tc_ok, lift] at hrun
      generalize hindex : core.array.Array.index_mut
          (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) input
          { start := Std.Usize.wrapping_add 1#usize
              (Std.Usize.wrapping_mul iter.start 32#usize),
            «end» := Std.Usize.wrapping_add 1#usize
              (Std.Usize.wrapping_mul
                (Std.Usize.wrapping_add iter.start 1#usize) 32#usize) } =
        indexResult at hrun
      cases indexResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok indexed =>
          rcases indexed with ⟨target, back⟩
          simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
          by_cases hpresent :
              present &&& Std.U8.wrapping_shl 1#u8
                (UScalar.cast .U32 iter.start) != 0#u8
          · rw [if_pos hpresent] at hrun
            generalize hget : core.slice.Slice.get
                (core.slice.index.SliceIndexUsizeSlice GeneratedDigest)
                (alloc.vec.Vec.deref level) valuePos = getResult at hrun
            cases getResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | ok valueOption =>
                cases valueOption with
                | none =>
                    change Result.ok
                      (next, nodePos, valuePos, some false, 0#u32) =
                      Result.ok (finalNext, finalNodePos, finalValuePos,
                        finalPending, 1#u32) at hrun
                    have hcode := congrArg (fun output => output.2.2.2.2)
                      (Result.ok.inj hrun)
                    norm_num at hcode
                | some child =>
                    simp only [Option.elim_some, Aeneas.Std.bind_tc_ok, lift]
                      at hrun
                    generalize hcopy : core.slice.Slice.copy_from_slice
                        core.marker.CopyU8 target (Array.to_slice child) =
                      copyResult at hrun
                    cases copyResult with
                    | fail error =>
                        change (.fail error : Result
                          (GeneratedDigestVec × Std.Usize × Std.Usize ×
                            Option Bool × Std.U32)) =
                          .ok (finalNext, finalNodePos, finalValuePos,
                            finalPending, 1#u32) at hrun
                        contradiction
                    | div =>
                        change (.div : Result
                          (GeneratedDigestVec × Std.Usize × Std.Usize ×
                            Option Bool × Std.U32)) =
                          .ok (finalNext, finalNodePos, finalValuePos,
                            finalPending, 1#u32) at hrun
                        contradiction
                    | ok copied =>
                        simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
                        have hgetOption :
                            level.val[valuePos.val]? = some child := by
                          change Result.ok level.val[valuePos.val]? =
                              Result.ok (some child) at hget
                          exact Result.ok.inj hget
                        rw [List.getElem?_eq_some_iff] at hgetOption
                        obtain ⟨hvalueBound, hchildAt⟩ := hgetOption
                        have hchildEq : child = level.val[valuePos.val]! := by
                          exact hchildAt.symm.trans
                            (List.Inhabited_getElem_eq_getElem!
                              level.val valuePos.val hvalueBound)
                        have hsourceLength :
                            (Array.to_slice child).val.length = 32 := by
                          simpa using child.property
                        have hwrite : rawWriteChildSlice input iter.start
                            (Array.to_slice child) = .ok (back copied) := by
                          unfold rawWriteChildSlice
                          simp only [lift, Aeneas.Std.bind_tc_ok]
                          rw [hindex]
                          simp only [Aeneas.Std.bind_tc_ok]
                          rw [hcopy]
                          simp only [Aeneas.Std.bind_tc_ok]
                        have hvalueRoom : valuePos.val + 1 <
                            UScalar.size .Usize := by
                          have hlength := level.property
                          have hsizes : UScalar.size .Usize = Usize.size :=
                            UScalar.size_UScalarTyUsize
                          have hmax : Usize.max < Usize.size := by
                            rcases System.Platform.numBits_eq with
                              hbits | hbits <;>
                                simp [Usize.max, Usize.size, Usize.numBits,
                                  hbits]
                          rw [hsizes]
                          omega
                        have hvalueSucc :
                            (Std.Usize.wrapping_add valuePos 1#usize).val =
                              valuePos.val + 1 :=
                          usize_succ_val valuePos hvalueRoom
                        have hfilled' : FilledChildPrefix (back copied)
                            (children ++ [child]) :=
                          filledChildPrefix_append input (back copied)
                            iter.start (Array.to_slice child) children child
                            hchildren.symm hslot hsourceLength rfl hfilled
                            hwrite
                        have hreads' : OrderedChildReads nodeBytes level
                            present (children ++ [child]).length startNodePos
                            startValuePos (children ++ [child]) nodePos
                            (Std.Usize.wrapping_add valuePos 1#usize) := by
                          simpa using OrderedChildReads.live iter.start child
                            (Std.Usize.wrapping_add valuePos 1#usize) hreads
                            hchildren.symm (by rw [hchildren]; exact hslot)
                            hpresent hvalueBound hchildEq
                            hvalueSucc
                        have hspan' : iter'.start.val + remaining =
                            iter'.end.val := by
                          rw [hiterStart, hiterEnd]
                          omega
                        have hend' : iter'.end.val = 4 := by
                          rw [hiterEnd]
                          exact hend
                        have hchildren' : (children ++ [child]).length =
                            iter'.start.val := by
                          simp only [List.length_append,
                            List.length_singleton]
                          rw [hchildren, hiterStart]
                        change
                          merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
                            iter' nodeBytes level next nodePos
                            (Std.Usize.wrapping_add valuePos 1#usize) present
                            (back copied) pending =
                          .ok (finalNext, finalNodePos, finalValuePos,
                            finalPending, 1#u32) at hrun
                        exact ih iter' nodePos
                          (Std.Usize.wrapping_add valuePos 1#usize)
                          (back copied) (children ++ [child]) hspan' hend'
                          hchildren' hreads' hfilled' hnodeLe hrun
          · rw [if_neg hpresent] at hrun
            have hnodeRoom : nodePos.val + 32 < UScalar.size .Usize := by
              omega
            have hnodeSucc :
                (Std.Usize.wrapping_add nodePos 32#usize).val =
                  nodePos.val + 32 :=
              usize_add_32_val nodePos hnodeRoom
            by_cases hpast :
                Std.Usize.wrapping_add nodePos 32#usize > Slice.len nodeBytes
            · rw [if_pos hpast] at hrun
              change Result.ok
                  (next, nodePos, valuePos, some false, 0#u32) =
                Result.ok (finalNext, finalNodePos, finalValuePos,
                  finalPending, 1#u32) at hrun
              have hcode := congrArg (fun output => output.2.2.2.2)
                (Result.ok.inj hrun)
              norm_num at hcode
            · rw [if_neg hpast] at hrun
              have hfrontierRoom :
                  nodePos.val + 32 ≤ nodeBytes.val.length := by
                change ¬ (Std.Usize.wrapping_add nodePos 32#usize).val >
                  nodeBytes.val.length at hpast
                rw [hnodeSucc] at hpast
                omega
              generalize hslice : core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                  nodeBytes
                  { start := nodePos,
                    «end» := Std.Usize.wrapping_add nodePos 32#usize } =
                sliceResult at hrun
              cases sliceResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | ok source =>
                  simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
                  generalize hcopy : core.slice.Slice.copy_from_slice
                      core.marker.CopyU8 target source = copyResult at hrun
                  cases copyResult with
                  | fail error =>
                      change (.fail error : Result
                        (GeneratedDigestVec × Std.Usize × Std.Usize ×
                          Option Bool × Std.U32)) =
                        .ok (finalNext, finalNodePos, finalValuePos,
                          finalPending, 1#u32) at hrun
                      contradiction
                  | div =>
                      change (.div : Result
                        (GeneratedDigestVec × Std.Usize × Std.Usize ×
                          Option Bool × Std.U32)) =
                        .ok (finalNext, finalNodePos, finalValuePos,
                          finalPending, 1#u32) at hrun
                      contradiction
                  | ok copied =>
                      simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
                      have hvalid :
                          nodePos ≤ Std.Usize.wrapping_add nodePos 32#usize ∧
                          Std.Usize.wrapping_add nodePos 32#usize ≤
                            Slice.len nodeBytes := by
                        constructor
                        · apply (UScalar.le_equiv _ _).2
                          rw [hnodeSucc]
                          omega
                        · apply (UScalar.le_equiv _ _).2
                          rw [hnodeSucc]
                          exact hfrontierRoom
                      have hslice' :
                          core.slice.index.SliceIndexRangeUsizeSlice.index
                            { start := nodePos,
                              «end» := Std.Usize.wrapping_add nodePos
                                32#usize }
                            nodeBytes = .ok source := by
                        exact hslice
                      obtain ⟨source', hsourceRun, hsourceVal', _⟩ :=
                        Aeneas.Std.WP.spec_imp_exists
                          (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
                            { start := nodePos,
                              «end» := Std.Usize.wrapping_add nodePos
                                32#usize }
                            nodeBytes hvalid.1 hvalid.2)
                      have hsourceEq : source' = source := Result.ok.inj
                        (hsourceRun.symm.trans hslice')
                      subst source'
                      have hsourceVal : source.val = nodeBytes.val.slice
                          nodePos.val
                          (Std.Usize.wrapping_add nodePos 32#usize).val := by
                        exact hsourceVal'
                      have hsourceLength : source.val.length = 32 := by
                        rw [hsourceVal, List.slice_length, hnodeSucc]
                        omega
                      let frontierChild : GeneratedDigest :=
                        Array.make 32#usize source.val (by
                          exact hsourceLength)
                      have hchildBytes : ∀ byte, byte < 32 →
                          frontierChild.val[byte]! =
                            nodeBytes.val[nodePos.val + byte]! := by
                        intro byte hbyte
                        change source.val[byte]! = _
                        rw [hsourceVal]
                        exact List.getElem!_slice nodePos.val
                          (Std.Usize.wrapping_add nodePos 32#usize).val byte
                          nodeBytes.val (by
                            constructor
                            · rw [hnodeSucc]
                              exact hfrontierRoom
                            · rw [hnodeSucc]
                              omega)
                      have hwrite : rawWriteChildSlice input iter.start
                          source = .ok (back copied) := by
                        unfold rawWriteChildSlice
                        simp only [lift, Aeneas.Std.bind_tc_ok]
                        rw [hindex]
                        simp only [Aeneas.Std.bind_tc_ok]
                        rw [hcopy]
                        simp only [Aeneas.Std.bind_tc_ok]
                      have hfilled' : FilledChildPrefix (back copied)
                          (children ++ [frontierChild]) :=
                        filledChildPrefix_append input (back copied)
                          iter.start source children frontierChild
                          hchildren.symm hslot hsourceLength rfl hfilled
                          hwrite
                      have hreads' : OrderedChildReads nodeBytes level
                          present (children ++ [frontierChild]).length
                          startNodePos startValuePos
                          (children ++ [frontierChild])
                          (Std.Usize.wrapping_add nodePos 32#usize)
                          valuePos := by
                        simpa using OrderedChildReads.frontier iter.start
                          frontierChild
                          (Std.Usize.wrapping_add nodePos 32#usize) hreads
                          hchildren.symm (by rw [hchildren]; exact hslot)
                          hpresent hfrontierRoom hchildBytes hnodeSucc
                      have hspan' : iter'.start.val + remaining =
                          iter'.end.val := by
                        rw [hiterStart, hiterEnd]
                        omega
                      have hend' : iter'.end.val = 4 := by
                        rw [hiterEnd]
                        exact hend
                      have hchildren' :
                          (children ++ [frontierChild]).length =
                            iter'.start.val := by
                        simp only [List.length_append, List.length_singleton]
                        rw [hchildren, hiterStart]
                      change
                        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
                          iter' nodeBytes level next
                          (Std.Usize.wrapping_add nodePos 32#usize) valuePos
                          present (back copied) pending =
                        .ok (finalNext, finalNodePos, finalValuePos,
                          finalPending, 1#u32) at hrun
                      exact ih iter'
                        (Std.Usize.wrapping_add nodePos 32#usize) valuePos
                        (back copied) (children ++ [frontierChild]) hspan'
                        hend' hchildren' hreads' hfilled'
                        (by rw [hnodeSucc]; exact hfrontierRoom) hrun

/-- Public four-slot theorem for the literal `0..4` range instantiated by
the unchanged generated Rust loop. -/
theorem unchanged_four_child_loop_success_yields_witness
    (sha256 : List ModelByte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (nodeBytes : Slice Std.U8) (level next finalNext : GeneratedDigestVec)
    (present : Std.U8) (pending finalPending : Option Bool)
    (nodePos valuePos finalNodePos finalValuePos : Std.Usize)
    (input : GeneratedRadixInput)
    (htag : input.val[0]! = merkle.DOM_NODE4)
    (hnodeLe : nodePos.val ≤ nodeBytes.val.length)
    (hroom : nodeBytes.val.length + 32 < UScalar.size .Usize)
    (hrun :
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
          { start := 0#usize, «end» := 4#usize }
          nodeBytes level next nodePos valuePos present input pending =
        .ok (finalNext, finalNodePos, finalValuePos, finalPending, 1#u32)) :
    finalPending = pending ∧
      Nonempty (RawChildHashWitness sha256 nodeBytes level present nodePos
        valuePos next finalNext finalNodePos finalValuePos) := by
  apply raw_child_loop_from_prefix
    (sha256 := sha256) (hhash := hhash) (remaining := 4)
    (iter := { start := 0#usize, «end» := 4#usize })
    (nodeBytes := nodeBytes) (level := level) (next := next)
    (finalNext := finalNext) (present := present) (pending := pending)
    (finalPending := finalPending) (startNodePos := nodePos)
    (startValuePos := valuePos) (nodePos := nodePos) (valuePos := valuePos)
    (finalNodePos := finalNodePos) (finalValuePos := finalValuePos)
    (hstartNode := hnodeLe) (hroom := hroom) (input := input)
    (children := [])
  · norm_num
  · norm_num
  · norm_num
  · exact OrderedChildReads.nil nodePos valuePos
  · exact empty_filled_child_prefix input htag
  · exact hnodeLe
  · exact hrun

/-- The unchanged four-child loop can preserve an existing `true` result or
replace it with `false`, but it never creates `true` from a non-`true`
pending value.  This covers both its normal and early-rejection exits. -/
private theorem child_loop_preserves_not_true_from_span
    (remaining : Nat) (iter : core.ops.range.Range Std.Usize)
    (nodeBytes : Slice Std.U8) (level next finalNext : GeneratedDigestVec)
    (present : Std.U8) (pending finalPending : Option Bool)
    (nodePos valuePos finalNodePos finalValuePos : Std.Usize)
    (input : GeneratedRadixInput) (finalCode : Std.U32)
    (hspan : remaining = iter.end.val - iter.start.val)
    (hnot : pending ≠ some true)
    (hrun :
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
          iter nodeBytes level next nodePos valuePos present input pending =
        .ok (finalNext, finalNodePos, finalValuePos, finalPending,
          finalCode)) :
    finalPending ≠ some true := by
  induction remaining generalizing iter nodePos valuePos input with
  | zero =>
      have hfinished : iter.end.val ≤ iter.start.val := by omega
      have hs := core.iter.range.IteratorRange.next_Usize_none_spec iter
        hfinished
      rcases Aeneas.Std.WP.spec_imp_exists hs with
        ⟨⟨option, iter'⟩, hnext, hoption, hiter⟩
      rw [hoption, hiter] at hnext
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
        at hrun
      rw [Aeneas.Std.loop.eq_def] at hrun
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0.body
        at hrun
      simp only [hnext, Aeneas.Std.bind_tc_ok, lift] at hrun
      generalize hhash : merkle.fixed_hashv
          (Array.to_slice
            (Array.make 1#usize [Array.to_slice input] (by rfl))) =
        hashResult at hrun
      cases hashResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok digest =>
          simp only [Aeneas.Std.bind_tc_ok] at hrun
          generalize hpush : alloc.vec.Vec.push next digest = pushResult at hrun
          cases pushResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok next' =>
              simp only [Aeneas.Std.bind_tc_ok] at hrun
              have hpending : pending = finalPending :=
                congrArg (fun output => output.2.2.2.1)
                  (Result.ok.inj hrun)
              intro htrue
              exact hnot (hpending.trans htrue)
  | succ remaining ih =>
      have hactive : iter.start.val < iter.end.val := by omega
      have hs := core.iter.range.IteratorRange.next_Usize_some_spec iter hactive
      rcases Aeneas.Std.WP.spec_imp_exists hs with
        ⟨⟨option, iter'⟩, hnext, hoption, hiterStart, hiterEnd⟩
      rw [hoption] at hnext
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
        at hrun
      rw [Aeneas.Std.loop.eq_def] at hrun
      simp only at hrun
      generalize hbody :
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0.body
          nodeBytes level next present pending iter nodePos valuePos input =
            bodyResult at hrun
      cases bodyResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok flow =>
          unfold
            merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0.body
            at hbody
          simp only [hnext, Aeneas.Std.bind_tc_ok, lift] at hbody
          generalize hindex : core.array.Array.index_mut
              (core.ops.index.IndexMutSlice
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) input
              { start := Std.Usize.wrapping_add 1#usize
                  (Std.Usize.wrapping_mul iter.start 32#usize),
                «end» := Std.Usize.wrapping_add 1#usize
                  (Std.Usize.wrapping_mul
                    (Std.Usize.wrapping_add iter.start 1#usize) 32#usize) } =
            indexResult at hbody
          cases indexResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hbody
          | div => simp [Bind.bind, Aeneas.Std.bind] at hbody
          | ok indexed =>
              rcases indexed with ⟨target, back⟩
              simp only [Aeneas.Std.bind_tc_ok, lift] at hbody
              by_cases hpresent :
                  present &&& Std.U8.wrapping_shl 1#u8
                    (UScalar.cast .U32 iter.start) != 0#u8
              · rw [if_pos hpresent] at hbody
                generalize hget : core.slice.Slice.get
                    (core.slice.index.SliceIndexUsizeSlice GeneratedDigest)
                    (alloc.vec.Vec.deref level) valuePos = getResult at hbody
                cases getResult with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at hbody
                | div => simp [Bind.bind, Aeneas.Std.bind] at hbody
                | ok valueOption =>
                    cases valueOption with
                    | none =>
                        have hflow := (Result.ok.inj hbody).symm
                        subst flow
                        simp only at hrun
                        intro htrue
                        have hpending := congrArg
                          (fun output => output.2.2.2.1)
                          (Result.ok.inj hrun)
                        simp [htrue] at hpending
                    | some child =>
                        simp only [Option.elim_some, Aeneas.Std.bind_tc_ok,
                          lift] at hbody
                        generalize hcopy : core.slice.Slice.copy_from_slice
                            core.marker.CopyU8 target (Array.to_slice child) =
                          copyResult at hbody
                        cases copyResult with
                        | fail error =>
                            simp [Bind.bind, Aeneas.Std.bind] at hbody
                        | div => simp [Bind.bind, Aeneas.Std.bind] at hbody
                        | ok copied =>
                            simp only [Aeneas.Std.bind_tc_ok, lift] at hbody
                            have hflow : flow = ControlFlow.cont
                                (iter', nodePos,
                                  Std.Usize.wrapping_add valuePos 1#usize,
                                  back copied) :=
                              (Result.ok.inj hbody).symm
                            subst flow
                            simp only at hrun
                            have hspan' : remaining =
                                iter'.end.val - iter'.start.val := by
                              rw [hiterStart, hiterEnd]
                              omega
                            change
                              merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
                                  iter' nodeBytes level next nodePos
                                  (Std.Usize.wrapping_add valuePos 1#usize)
                                  present (back copied) pending =
                                .ok (finalNext, finalNodePos, finalValuePos,
                                  finalPending, finalCode) at hrun
                            exact ih iter' nodePos
                              (Std.Usize.wrapping_add valuePos 1#usize)
                              (back copied) hspan' hrun
              · rw [if_neg hpresent] at hbody
                by_cases hpast : Std.Usize.wrapping_add nodePos 32#usize >
                    Slice.len nodeBytes
                · rw [if_pos hpast] at hbody
                  have hflow := (Result.ok.inj hbody).symm
                  subst flow
                  simp only at hrun
                  intro htrue
                  have hpending := congrArg (fun output => output.2.2.2.1)
                    (Result.ok.inj hrun)
                  simp [htrue] at hpending
                · rw [if_neg hpast] at hbody
                  generalize hslice : core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                      nodeBytes
                      { start := nodePos,
                        «end» := Std.Usize.wrapping_add nodePos 32#usize } =
                    sliceResult at hbody
                  cases sliceResult with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hbody
                  | div => simp [Bind.bind, Aeneas.Std.bind] at hbody
                  | ok source =>
                      simp only [Aeneas.Std.bind_tc_ok, lift] at hbody
                      generalize hcopy : core.slice.Slice.copy_from_slice
                          core.marker.CopyU8 target source = copyResult at hbody
                      cases copyResult with
                      | fail error =>
                          simp [Bind.bind, Aeneas.Std.bind] at hbody
                      | div => simp [Bind.bind, Aeneas.Std.bind] at hbody
                      | ok copied =>
                          simp only [Aeneas.Std.bind_tc_ok, lift] at hbody
                          have hflow : flow = ControlFlow.cont
                              (iter', Std.Usize.wrapping_add nodePos 32#usize,
                                valuePos, back copied) :=
                            (Result.ok.inj hbody).symm
                          subst flow
                          simp only at hrun
                          have hspan' : remaining =
                              iter'.end.val - iter'.start.val := by
                            rw [hiterStart, hiterEnd]
                            omega
                          change
                            merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
                                iter' nodeBytes level next
                                (Std.Usize.wrapping_add nodePos 32#usize)
                                valuePos present (back copied) pending =
                              .ok (finalNext, finalNodePos, finalValuePos,
                                finalPending, finalCode) at hrun
                          exact ih iter'
                            (Std.Usize.wrapping_add nodePos 32#usize) valuePos
                            (back copied) hspan' hrun

private theorem slice_iterator_next_some (iter : core.slice.iter.Iter Std.U8)
    (hactive : iter.i < iter.slice.val.length) :
    core.slice.iter.IteratorSliceIter.next iter =
      .ok (some iter.slice.val[iter.i]!,
        { slice := iter.slice, i := iter.i + 1 }) := by
  unfold core.slice.iter.IteratorSliceIter.next
  rw [dif_pos (by simpa [Slice.len, Slice.length] using hactive)]
  simp only
  apply congrArg (fun value : Std.U8 =>
    (Result.ok (some value,
      ({ slice := iter.slice, i := iter.i + 1 } :
        core.slice.iter.Iter Std.U8)) :
      Result (Option Std.U8 × core.slice.iter.Iter Std.U8)))
  exact (Slice.getElem_Nat_eq iter.slice iter.i hactive).trans
    (List.Inhabited_getElem_eq_getElem! _ _ hactive)

private theorem zero_pattern_eq_zero_u32 :
    (0#32#uscalar : Std.U32) = 0#u32 := by
  apply UScalar.eq_of_val_eq
  rfl

private theorem one_pattern_eq_one_u32 :
    (1#32#uscalar : Std.U32) = 1#u32 := by
  apply UScalar.eq_of_val_eq
  rfl

/-! ## The unchanged mask/group loop -/

/-- Exact successful trace of the unchanged loop over the mask bytes of one
radix level.  Each `step` contains the four ordered child reads and the exact
radix-four SHA-256 equation obtained above.  The terminal constructor records
the production all-values-consumed check and scratch-vector swap. -/
inductive RawGroupTrace
    (sha256 : List ModelByte → Digest32)
    (nodeBytes : Slice Std.U8) (level : GeneratedDigestVec) :
    core.slice.iter.Iter Std.U8 → GeneratedDigestVec → Std.Usize →
      Std.Usize → Option Bool → GeneratedDigestVec → GeneratedDigestVec →
      Std.Usize → Option Bool → Prop
  | done (iter : core.slice.iter.Iter Std.U8)
      (next : GeneratedDigestVec) (nodePos valuePos : Std.Usize)
      (pending : Option Bool)
      (iterator_finished : iter.slice.val.length ≤ iter.i)
      (values_consumed : valuePos = alloc.vec.Vec.len level) :
      RawGroupTrace sha256 nodeBytes level iter next nodePos valuePos pending
        (core.mem.swap level next).1 (core.mem.swap level next).2 nodePos
        pending
  | step (iter iter' : core.slice.iter.Iter Std.U8) (present : Std.U8)
      (next next' finalLevel finalNext : GeneratedDigestVec)
      (nodePos valuePos nodePos' valuePos' finalNodePos : Std.Usize)
      (pending pending' finalPending : Option Bool)
      (input : GeneratedRadixInput)
      (iterator_next : core.slice.iter.IteratorSliceIter.next iter =
        .ok (some present, iter'))
      (input_init : Array.update (Array.repeat 129#usize 0#u8) 0#usize
        merkle.DOM_NODE4 = .ok input)
      (children_run :
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
          { start := 0#usize, «end» := 4#usize } nodeBytes level next nodePos
          valuePos present input pending =
        .ok (next', nodePos', valuePos', pending', 1#u32))
      (pending_unchanged : pending' = pending)
      (children : RawChildHashWitness sha256 nodeBytes level present nodePos
        valuePos next next' nodePos' valuePos')
      (tail : RawGroupTrace sha256 nodeBytes level iter' next' nodePos'
        valuePos' pending' finalLevel finalNext finalNodePos finalPending) :
      RawGroupTrace sha256 nodeBytes level iter next nodePos valuePos pending
        finalLevel finalNext finalNodePos finalPending

private theorem raw_group_loop_from_span
    (sha256 : List ModelByte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (remaining : Nat) (iter : core.slice.iter.Iter Std.U8)
    (nodeBytes : Slice Std.U8) (level next : GeneratedDigestVec)
    (nodePos valuePos : Std.Usize) (pending : Option Bool)
    (finalLevel finalNext : GeneratedDigestVec)
    (finalNodePos : Std.Usize) (finalPending : Option Bool)
    (hspan : remaining = iter.slice.val.length - iter.i)
    (hnodeLe : nodePos.val ≤ nodeBytes.val.length)
    (hroom : nodeBytes.val.length + 32 < UScalar.size .Usize)
    (hrun :
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0
          iter nodeBytes level next nodePos valuePos pending =
        .ok (finalLevel, finalNext, finalNodePos, finalPending, 1#u32)) :
    Nonempty (RawGroupTrace sha256 nodeBytes level iter next nodePos valuePos
      pending finalLevel finalNext finalNodePos finalPending) := by
  induction remaining generalizing iter next nodePos valuePos pending with
  | zero =>
      have hfinished : iter.slice.val.length ≤ iter.i := by omega
      have hnext : core.slice.iter.IteratorSliceIter.next iter =
          .ok (none, iter) := by
        simp [core.slice.iter.IteratorSliceIter.next, Slice.len,
          Slice.length, hfinished]
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0 at hrun
      rw [Aeneas.Std.loop.eq_def] at hrun
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0.body
        at hrun
      simp only [hnext, Aeneas.Std.bind_tc_ok, lift] at hrun
      by_cases hconsumed : valuePos = alloc.vec.Vec.len level
      · have hneq : (valuePos != alloc.vec.Vec.len level) = false := by
          simp [hconsumed]
        rw [hneq] at hrun
        simp only [Bool.false_eq_true, if_false] at hrun
        have hout := Result.ok.inj hrun
        have hlevel : (core.mem.swap level next).1 = finalLevel :=
          congrArg (fun output => output.1) hout
        have hnextOut : (core.mem.swap level next).2 = finalNext :=
          congrArg (fun output => output.2.1) hout
        have hnode : nodePos = finalNodePos :=
          congrArg (fun output => output.2.2.1) hout
        have hpending : pending = finalPending :=
          congrArg (fun output => output.2.2.2.1) hout
        subst finalLevel
        subst finalNext
        subst finalNodePos
        subst finalPending
        exact ⟨RawGroupTrace.done iter next nodePos valuePos pending hfinished
          hconsumed⟩
      · have hneq : (valuePos != alloc.vec.Vec.len level) = true := by
          simp [hconsumed]
        rw [hneq] at hrun
        simp at hrun
  | succ remaining ih =>
      have hactive : iter.i < iter.slice.val.length := by omega
      let present : Std.U8 := iter.slice.val[iter.i]!
      let iter' : core.slice.iter.Iter Std.U8 :=
        { slice := iter.slice, i := iter.i + 1 }
      have hnext : core.slice.iter.IteratorSliceIter.next iter =
          .ok (some present, iter') := by
        simpa [present, iter'] using slice_iterator_next_some iter hactive
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0 at hrun
      rw [Aeneas.Std.loop.eq_def] at hrun
      simp only at hrun
      generalize hbody :
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0.body
          nodeBytes level iter next nodePos valuePos pending = bodyResult at hrun
      cases bodyResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok flow =>
          unfold
            merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0.body
            at hbody
          simp only [hnext, Aeneas.Std.bind_tc_ok, lift] at hbody
          generalize hinit :
            Array.update (Array.repeat 129#usize 0#u8) 0#usize
              merkle.DOM_NODE4 = inputResult at hbody
          cases inputResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hbody
          | div => simp [Bind.bind, Aeneas.Std.bind] at hbody
          | ok input =>
              simp only [Aeneas.Std.bind_tc_ok] at hbody
              generalize hchildren :
                merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
                  { start := 0#usize, «end» := 4#usize } nodeBytes level next
                  nodePos valuePos present input pending = childrenResult at hbody
              cases childrenResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hbody
              | div => simp [Bind.bind, Aeneas.Std.bind] at hbody
              | ok childrenOutput =>
                  rcases childrenOutput with
                    ⟨next', nodePos', valuePos', pending', code⟩
                  simp only [Aeneas.Std.bind_tc_ok] at hbody
                  split at hbody
                  next codeOne =>
                    have hflow : flow = ControlFlow.cont
                        (iter', next', nodePos', valuePos', pending') :=
                      (Result.ok.inj hbody).symm
                    subst flow
                    simp only at hrun
                    have hchildrenOne :
                        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
                            { start := 0#usize, «end» := 4#usize }
                            nodeBytes level next nodePos valuePos present input
                            pending =
                          .ok (next', nodePos', valuePos', pending', 1#u32) := by
                      rw [one_pattern_eq_one_u32] at hchildren
                      exact hchildren
                    have htag : input.val[0]! = merkle.DOM_NODE4 := by
                      have hinitValue := Result.ok.inj hinit
                      simp [Array.update, core.array.Array.index_mut,
                        core.ops.index.IndexMutSlice,
                        core.slice.index.Slice.index_mut, List.set]
                        at hinitValue
                      simpa using
                        (congrArg (fun value => value.val[0]!) hinitValue).symm
                    obtain ⟨hpending, ⟨children⟩⟩ :=
                      unchanged_four_child_loop_success_yields_witness sha256
                        hhash nodeBytes level next next' present pending pending'
                        nodePos valuePos nodePos' valuePos' input htag hnodeLe
                        hroom hchildrenOne
                    have hnextNode : nodePos'.val ≤ nodeBytes.val.length :=
                      children.ordered_reads.finalNodePos_le hnodeLe
                    have hspan' : remaining =
                        iter'.slice.val.length - iter'.i := by
                      simp only [iter']
                      omega
                    change
                      merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0
                        iter' nodeBytes level next' nodePos' valuePos' pending' =
                        .ok (finalLevel, finalNext, finalNodePos, finalPending,
                          1#u32) at hrun
                    let tail := Classical.choice
                      (ih iter' next' nodePos' valuePos' pending' hspan'
                        hnextNode hrun)
                    exact ⟨RawGroupTrace.step iter iter' present next next'
                      finalLevel finalNext nodePos valuePos nodePos' valuePos'
                      finalNodePos pending pending' finalPending input hnext hinit
                      hchildrenOne hpending children tail⟩
                  next codeOther =>
                    cases pending' with
                    | none =>
                        have hflow := (Result.ok.inj hbody).symm
                        subst flow
                        simp at hrun
                    | some accepted =>
                        have hflow := (Result.ok.inj hbody).symm
                        subst flow
                        simp at hrun

/-- Every accepting run of the unchanged mask iterator exposes one exact
four-child witness per mask and ends only after consuming all live values. -/
theorem unchanged_group_loop_success_yields_trace
    (sha256 : List ModelByte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (iter : core.slice.iter.Iter Std.U8)
    (nodeBytes : Slice Std.U8) (level next : GeneratedDigestVec)
    (nodePos valuePos : Std.Usize) (pending : Option Bool)
    (finalLevel finalNext : GeneratedDigestVec)
    (finalNodePos : Std.Usize) (finalPending : Option Bool)
    (hnodeLe : nodePos.val ≤ nodeBytes.val.length)
    (hroom : nodeBytes.val.length + 32 < UScalar.size .Usize)
    (hrun :
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0 iter
          nodeBytes level next nodePos valuePos pending =
        .ok (finalLevel, finalNext, finalNodePos, finalPending, 1#u32)) :
    Nonempty (RawGroupTrace sha256 nodeBytes level iter next nodePos valuePos
      pending finalLevel finalNext finalNodePos finalPending) := by
  apply raw_group_loop_from_span sha256 hhash
    (iter.slice.val.length - iter.i) iter nodeBytes level next nodePos valuePos
    pending finalLevel finalNext finalNodePos finalPending
  · rfl
  · exact hnodeLe
  · exact hroom
  · exact hrun

theorem RawGroupTrace.finalPending_eq
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    {iter : core.slice.iter.Iter Std.U8} {next : GeneratedDigestVec}
    {nodePos valuePos : Std.Usize} {pending : Option Bool}
    {finalLevel finalNext : GeneratedDigestVec} {finalNodePos : Std.Usize}
    {finalPending : Option Bool}
    (trace : RawGroupTrace sha256 nodeBytes level iter next nodePos valuePos
      pending finalLevel finalNext finalNodePos finalPending) :
    finalPending = pending := by
  induction trace with
  | done => rfl
  | step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pending_eq _ _ ih =>
      exact ih.trans pending_eq

theorem RawGroupTrace.finalNodePos_le
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    {iter : core.slice.iter.Iter Std.U8} {next : GeneratedDigestVec}
    {nodePos valuePos : Std.Usize} {pending : Option Bool}
    {finalLevel finalNext : GeneratedDigestVec} {finalNodePos : Std.Usize}
    {finalPending : Option Bool}
    (trace : RawGroupTrace sha256 nodeBytes level iter next nodePos valuePos
      pending finalLevel finalNext finalNodePos finalPending)
    (hstart : nodePos.val ≤ nodeBytes.val.length) :
    finalNodePos.val ≤ nodeBytes.val.length := by
  induction trace with
  | done => exact hstart
  | step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ children tail ih =>
      exact ih (children.ordered_reads.finalNodePos_le hstart)

/-- The mask loop likewise never creates a pending `true`: it either carries
the value supplied to it, or records `false` on a rejected child/frontier
read. -/
private theorem group_loop_preserves_not_true_from_span
    (remaining : Nat) (iter : core.slice.iter.Iter Std.U8)
    (nodeBytes : Slice Std.U8) (level next finalLevel finalNext :
      GeneratedDigestVec)
    (nodePos valuePos finalNodePos : Std.Usize)
    (pending finalPending : Option Bool) (finalCode : Std.U32)
    (hspan : remaining = iter.slice.val.length - iter.i)
    (hnot : pending ≠ some true)
    (hrun :
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0 iter
          nodeBytes level next nodePos valuePos pending =
        .ok (finalLevel, finalNext, finalNodePos, finalPending, finalCode)) :
    finalPending ≠ some true := by
  induction remaining generalizing iter next nodePos valuePos pending with
  | zero =>
      have hfinished : iter.slice.val.length ≤ iter.i := by omega
      have hnext : core.slice.iter.IteratorSliceIter.next iter =
          .ok (none, iter) := by
        simp [core.slice.iter.IteratorSliceIter.next, Slice.len,
          Slice.length, hfinished]
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0 at hrun
      rw [Aeneas.Std.loop.eq_def] at hrun
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0.body
        at hrun
      simp only [hnext, Aeneas.Std.bind_tc_ok, lift] at hrun
      by_cases hconsumed : valuePos = alloc.vec.Vec.len level
      · have hneq : (valuePos != alloc.vec.Vec.len level) = false := by
          simp [hconsumed]
        rw [hneq] at hrun
        simp only [Bool.false_eq_true, if_false] at hrun
        have hpending : pending = finalPending :=
          congrArg (fun output => output.2.2.2.1) (Result.ok.inj hrun)
        intro htrue
        exact hnot (hpending.trans htrue)
      · have hneq : (valuePos != alloc.vec.Vec.len level) = true := by
          simp [hconsumed]
        rw [hneq] at hrun
        simp only [if_true] at hrun
        intro htrue
        have hpending := congrArg (fun output => output.2.2.2.1)
          (Result.ok.inj hrun)
        simp [htrue] at hpending
  | succ remaining ih =>
      have hactive : iter.i < iter.slice.val.length := by omega
      let present : Std.U8 := iter.slice.val[iter.i]!
      let iter' : core.slice.iter.Iter Std.U8 :=
        { slice := iter.slice, i := iter.i + 1 }
      have hnext : core.slice.iter.IteratorSliceIter.next iter =
          .ok (some present, iter') := by
        simpa [present, iter'] using slice_iterator_next_some iter hactive
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0 at hrun
      rw [Aeneas.Std.loop.eq_def] at hrun
      simp only at hrun
      generalize hbody :
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0.body
          nodeBytes level iter next nodePos valuePos pending = bodyResult at hrun
      cases bodyResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok flow =>
          unfold
            merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0.body
            at hbody
          simp only [hnext, Aeneas.Std.bind_tc_ok, lift] at hbody
          generalize hinit :
            Array.update (Array.repeat 129#usize 0#u8) 0#usize
              merkle.DOM_NODE4 = inputResult at hbody
          cases inputResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hbody
          | div => simp [Bind.bind, Aeneas.Std.bind] at hbody
          | ok input =>
              simp only [Aeneas.Std.bind_tc_ok] at hbody
              generalize hchildren :
                merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0_loop0
                  { start := 0#usize, «end» := 4#usize } nodeBytes level next
                  nodePos valuePos present input pending = childrenResult at hbody
              cases childrenResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hbody
              | div => simp [Bind.bind, Aeneas.Std.bind] at hbody
              | ok childrenOutput =>
                  rcases childrenOutput with
                    ⟨next', nodePos', valuePos', pending', code⟩
                  simp only [Aeneas.Std.bind_tc_ok] at hbody
                  have hpendingNot : pending' ≠ some true :=
                    child_loop_preserves_not_true_from_span 4
                      { start := 0#usize, «end» := 4#usize }
                      nodeBytes level next next' present pending pending'
                      nodePos valuePos nodePos' valuePos' input code (by
                        norm_num) hnot hchildren
                  split at hbody
                  next codeOne =>
                    have hflow : flow = ControlFlow.cont
                        (iter', next', nodePos', valuePos', pending') :=
                      (Result.ok.inj hbody).symm
                    subst flow
                    simp only at hrun
                    have hspan' : remaining =
                        iter'.slice.val.length - iter'.i := by
                      simp only [iter']
                      omega
                    change
                      merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0
                          iter' nodeBytes level next' nodePos' valuePos'
                          pending' =
                        .ok (finalLevel, finalNext, finalNodePos, finalPending,
                          finalCode) at hrun
                    exact ih iter' next' nodePos' valuePos' pending' hspan'
                      hpendingNot hrun
                  next codeOther =>
                    cases pending' with
                    | none =>
                        have hflow := (Result.ok.inj hbody).symm
                        subst flow
                        simp only at hrun
                        intro htrue
                        have hpending := congrArg
                          (fun output => output.2.2.2.1)
                          (Result.ok.inj hrun)
                        simp [htrue] at hpending
                    | some accepted =>
                        have hflow := (Result.ok.inj hbody).symm
                        subst flow
                        simp only at hrun
                        intro htrue
                        have hpending : accepted = true :=
                          Option.some.inj (congrArg
                            (fun output => output.2.2.2.1)
                            (Result.ok.inj hrun) |>.trans htrue)
                        exact hpendingNot (by simpa [hpending])

/-! ## The unchanged terminal root check -/

/-- Exact source of the two children used by an accepted odd-depth cap in the
unchanged generated loop. -/
inductive RawOddCapLocation
    (nodeBytes : Slice Std.U8) (indices : Slice Std.U32)
    (level : GeneratedDigestVec) (nodePos : Std.Usize) :
    GeneratedDigest → GeneratedDigest → Prop
  | both (levelSlice : Slice GeneratedDigest)
      (left right : GeneratedDigest)
      (level_slice_run : alloc.vec.Vec.as_slice Global level = .ok levelSlice)
      (indices_length : Slice.len indices = 2#usize)
      (level_length : Slice.len levelSlice = 2#usize)
      (left_index_run : Slice.index_usize indices 0#usize = .ok 0#u32)
      (right_index_run : Slice.index_usize indices 1#usize = .ok 1#u32)
      (left_run : Slice.index_usize levelSlice 0#usize = .ok left)
      (right_run : Slice.index_usize levelSlice 1#usize = .ok right)
      (frontier_consumed : nodePos = Slice.len nodeBytes) :
      RawOddCapLocation nodeBytes indices level nodePos left right
  | liveLeft (levelSlice : Slice GeneratedDigest)
      (value sibling : GeneratedDigest) (siblingSlice : Slice Std.U8)
      (level_slice_run : alloc.vec.Vec.as_slice Global level = .ok levelSlice)
      (indices_length : Slice.len indices = 1#usize)
      (level_length : Slice.len levelSlice = 1#usize)
      (index_run : Slice.index_usize indices 0#usize = .ok 0#u32)
      (value_run : Slice.index_usize levelSlice 0#usize = .ok value)
      (sibling_slice_run : core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) nodeBytes
        { start := nodePos,
          «end» := Std.Usize.wrapping_add nodePos 32#usize } =
        .ok siblingSlice)
      (sibling_copy_run :
        core.array.TryFromArrayCopySlice.try_from 32#usize
          core.marker.CopyU8 siblingSlice = .ok (.Ok sibling))
      (frontier_consumed : Std.Usize.wrapping_add nodePos 32#usize =
        Slice.len nodeBytes) :
      RawOddCapLocation nodeBytes indices level nodePos value sibling
  | liveRight (levelSlice : Slice GeneratedDigest)
      (value sibling : GeneratedDigest) (siblingSlice : Slice Std.U8)
      (level_slice_run : alloc.vec.Vec.as_slice Global level = .ok levelSlice)
      (indices_length : Slice.len indices = 1#usize)
      (level_length : Slice.len levelSlice = 1#usize)
      (index_run : Slice.index_usize indices 0#usize = .ok 1#u32)
      (value_run : Slice.index_usize levelSlice 0#usize = .ok value)
      (sibling_slice_run : core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) nodeBytes
        { start := nodePos,
          «end» := Std.Usize.wrapping_add nodePos 32#usize } =
        .ok siblingSlice)
      (sibling_copy_run :
        core.array.TryFromArrayCopySlice.try_from 32#usize
          core.marker.CopyU8 siblingSlice = .ok (.Ok sibling))
      (frontier_consumed : Std.Usize.wrapping_add nodePos 32#usize =
        Slice.len nodeBytes) :
      RawOddCapLocation nodeBytes indices level nodePos sibling value

/-- The exact accepted final root check.  The even case compares the sole top
node directly; the odd case hashes the exact pair selected by the production
indices/frontier logic. -/
inductive RawFinalRootWitness
    (sha256 : List ModelByte → Digest32)
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (topology : merkle.Radix4BinaryCapTopology)
    (binaryDepth : Std.U32) (level : GeneratedDigestVec)
    (nodePos : Std.Usize) : Prop
  | even (indices : Slice Std.U32) (levelSlice : Slice GeneratedDigest)
      (value : GeneratedDigest)
      (indices_run : merkle.Radix4BinaryCapTopology.impl.level_indices
        topology topology.radix_levels = .ok (some indices))
      (parity : binaryDepth &&& 1#u32 = 0#u32)
      (level_slice_run : alloc.vec.Vec.as_slice Global level = .ok levelSlice)
      (indices_length : Slice.len indices = 1#usize)
      (level_length : Slice.len levelSlice = 1#usize)
      (index_run : Slice.index_usize indices 0#usize = .ok 0#u32)
      (value_run : Slice.index_usize levelSlice 0#usize = .ok value)
      (frontier_consumed : nodePos = Slice.len nodeBytes)
      (root_eq : generatedArrayToDigest value = generatedArrayToDigest root) :
      RawFinalRootWitness sha256 root nodeBytes topology binaryDepth level
        nodePos
  | odd (indices : Slice Std.U32) (left right : GeneratedDigest)
      (indices_run : merkle.Radix4BinaryCapTopology.impl.level_indices
        topology topology.radix_levels = .ok (some indices))
      (parity : ¬ binaryDepth &&& 1#u32 = 0#u32)
      (location : RawOddCapLocation nodeBytes indices level nodePos left right)
      (root_eq : (sha256MerkleHashing sha256).binaryNode
        (generatedArrayToDigest left) (generatedArrayToDigest right) =
        generatedArrayToDigest root) :
      RawFinalRootWitness sha256 root nodeBytes topology binaryDepth level
        nodePos

/-- Literal terminal arm of the unchanged outer loop.  This is a local
factoring of the generated expression, used only so the four accepted root
shapes can be inverted without duplicating the enclosing iterator proof. -/
private abbrev RootLoopState :=
  core.ops.range.Range Std.Usize × GeneratedDigestVec ×
    GeneratedDigestVec × Std.Usize × Option Bool

private abbrev RootOutput :=
  GeneratedDigestVec × GeneratedDigestVec × Option Bool

private def doneMap (result : Result RootOutput) :
    Result (ControlFlow RootLoopState RootOutput) :=
  Bind.bind result (fun output => .ok (.done output))

private def rawEvenRootCheck
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (indices : Slice Std.U32) (level next : GeneratedDigestVec)
    (nodePos : Std.Usize) (pending : Option Bool) : Result RootOutput := do
  let levelSlice ← alloc.vec.Vec.as_slice Global level
  if Slice.len indices = 1#usize then
    if Slice.len levelSlice = 1#usize then
      let index ← Slice.index_usize indices 0#usize
      match index with
      | 0#uscalar =>
        let value ← Slice.index_usize levelSlice 0#usize
        if nodePos = Slice.len nodeBytes then
          let equal ← core.array.equality.PartialEqArray.eq
            core.cmp.PartialEqU8 value root
          .ok (level, next, some equal)
        else .ok (level, next, some false)
      | _ => .ok (level, next, pending)
    else .ok (level, next, pending)
  else .ok (level, next, pending)

private def sourceEvenRootCheck
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (indices : Slice Std.U32) (level next : GeneratedDigestVec)
    (nodePos : Std.Usize) (pending : Option Bool) :
    Result (ControlFlow RootLoopState RootOutput) := do
  let levelSlice ← alloc.vec.Vec.as_slice Global level
  if Slice.len indices = 1#usize then
    if Slice.len levelSlice = 1#usize then
      let index ← Slice.index_usize indices 0#usize
      match index with
      | 0#uscalar =>
        let value ← Slice.index_usize levelSlice 0#usize
        if nodePos = Slice.len nodeBytes then
          let equal ← core.array.equality.PartialEqArray.eq
            core.cmp.PartialEqU8 value root
          .ok (.done (level, next, some equal))
        else .ok (.done (level, next, some false))
      | _ => .ok (.done (level, next, pending))
    else .ok (.done (level, next, pending))
  else .ok (.done (level, next, pending))

private theorem sourceEvenRootCheck_eq_doneMap
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (indices : Slice Std.U32) (level next : GeneratedDigestVec)
    (nodePos : Std.Usize) (pending : Option Bool) :
    sourceEvenRootCheck root nodeBytes indices level next nodePos pending =
      doneMap (rawEvenRootCheck root nodeBytes indices level next nodePos
        pending) := by
  unfold sourceEvenRootCheck doneMap rawEvenRootCheck
  rw [Aeneas.Std.bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).2
  intro levelSlice hlevelSlice
  by_cases hindicesLen : Slice.len indices = 1#usize
  · simp only [hindicesLen, if_true]
    by_cases hlevelLen : Slice.len levelSlice = 1#usize
    · simp only [hlevelLen, if_true]
      rw [Aeneas.Std.bind_assoc_eq]
      apply (Aeneas.Std.bind_eq_iff _ _ _).2
      intro index hindex
      split
      next hzero =>
        rw [Aeneas.Std.bind_assoc_eq]
        apply (Aeneas.Std.bind_eq_iff _ _ _).2
        intro value hvalue
        by_cases hcursor : nodePos = Slice.len nodeBytes
        · simp only [hcursor, if_true]
          rw [Aeneas.Std.bind_assoc_eq]
          apply (Aeneas.Std.bind_eq_iff _ _ _).2
          intro equal hequal
          rfl
        · simp only [hcursor, if_false]
          rfl
      next hother => rfl
    · simp only [hlevelLen, if_false]
      rfl
  · simp only [hindicesLen, if_false]
    rfl

private noncomputable def rawOddTwoRootCheck
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (indices : Slice Std.U32) (levelSlice : Slice GeneratedDigest)
    (level next : GeneratedDigestVec) (nodePos : Std.Usize)
    (pending : Option Bool) : Result RootOutput := do
  if Slice.len levelSlice = 2#usize then
    let first ← Slice.index_usize indices 0#usize
    match first with
    | 0#uscalar =>
      let second ← Slice.index_usize indices 1#usize
      match second with
      | 1#uscalar =>
        let left ← Slice.index_usize levelSlice 0#usize
        let right ← Slice.index_usize levelSlice 1#usize
        let top ← merkle.fixed_node_hash left right
        if nodePos = Slice.len nodeBytes then
          let equal ← core.array.equality.PartialEqArray.eq
            core.cmp.PartialEqU8 top root
          .ok (level, next, some equal)
        else .ok (level, next, some false)
      | _ => .ok (level, next, pending)
    | _ => .ok (level, next, pending)
  else .ok (level, next, pending)

private noncomputable def sourceOddTwoRootCheck
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (indices : Slice Std.U32) (levelSlice : Slice GeneratedDigest)
    (level next : GeneratedDigestVec) (nodePos : Std.Usize)
    (pending : Option Bool) : Result (ControlFlow RootLoopState RootOutput) := do
  if Slice.len levelSlice = 2#usize then
    let first ← Slice.index_usize indices 0#usize
    match first with
    | 0#uscalar =>
      let second ← Slice.index_usize indices 1#usize
      match second with
      | 1#uscalar =>
        let left ← Slice.index_usize levelSlice 0#usize
        let right ← Slice.index_usize levelSlice 1#usize
        let top ← merkle.fixed_node_hash left right
        if nodePos = Slice.len nodeBytes then
          let equal ← core.array.equality.PartialEqArray.eq
            core.cmp.PartialEqU8 top root
          .ok (.done (level, next, some equal))
        else .ok (.done (level, next, some false))
      | _ => .ok (.done (level, next, pending))
    | _ => .ok (.done (level, next, pending))
  else .ok (.done (level, next, pending))

private theorem sourceOddTwoRootCheck_eq_doneMap
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (indices : Slice Std.U32) (levelSlice : Slice GeneratedDigest)
    (level next : GeneratedDigestVec) (nodePos : Std.Usize)
    (pending : Option Bool) :
    sourceOddTwoRootCheck root nodeBytes indices levelSlice level next nodePos
        pending =
      doneMap (rawOddTwoRootCheck root nodeBytes indices levelSlice level next
        nodePos pending) := by
  unfold sourceOddTwoRootCheck doneMap rawOddTwoRootCheck
  by_cases hlevelLen : Slice.len levelSlice = 2#usize
  · simp only [hlevelLen, if_true]
    rw [Aeneas.Std.bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).2
    intro first hfirst
    split
    next hfirstZero =>
      rw [Aeneas.Std.bind_assoc_eq]
      apply (Aeneas.Std.bind_eq_iff _ _ _).2
      intro second hsecond
      split
      next hsecondOne =>
        rw [Aeneas.Std.bind_assoc_eq]
        apply (Aeneas.Std.bind_eq_iff _ _ _).2
        intro left hleft
        rw [Aeneas.Std.bind_assoc_eq]
        apply (Aeneas.Std.bind_eq_iff _ _ _).2
        intro right hright
        rw [Aeneas.Std.bind_assoc_eq]
        apply (Aeneas.Std.bind_eq_iff _ _ _).2
        intro top htop
        by_cases hcursor : nodePos = Slice.len nodeBytes
        · simp only [hcursor, if_true]
          rw [Aeneas.Std.bind_assoc_eq]
          apply (Aeneas.Std.bind_eq_iff _ _ _).2
          intro equal hequal
          rfl
        · simp only [hcursor, if_false]
          rfl
      next hsecondOther => rfl
    next hfirstOther => rfl
  · simp only [hlevelLen, if_false]
    rfl

private noncomputable def rawOddOneRootCheck
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (indices : Slice Std.U32) (levelSlice : Slice GeneratedDigest)
    (level next : GeneratedDigestVec) (nodePos : Std.Usize)
    (pending : Option Bool) : Result RootOutput := do
  if Slice.len indices = 1#usize then
    if Slice.len levelSlice = 1#usize then
      let index ← Slice.index_usize indices 0#usize
      let value ← Slice.index_usize levelSlice 0#usize
      let endPos := Std.Usize.wrapping_add nodePos 32#usize
      if endPos > Slice.len nodeBytes then .ok (level, next, pending)
      else
        let siblingSlice ← core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) nodeBytes
          { start := nodePos, «end» := endPos }
        let copied ← core.array.TryFromArrayCopySlice.try_from 32#usize
          core.marker.CopyU8 siblingSlice
        let sibling ← core.result.Result.unwrap
          core.fmt.DebugTryFromSliceError copied
        if index = 0#u32 then
          let top ← merkle.fixed_node_hash value sibling
          if endPos = Slice.len nodeBytes then
            let equal ← core.array.equality.PartialEqArray.eq
              core.cmp.PartialEqU8 top root
            .ok (level, next, some equal)
          else .ok (level, next, some false)
        else if index = 1#u32 then
          let top ← merkle.fixed_node_hash sibling value
          if endPos = Slice.len nodeBytes then
            let equal ← core.array.equality.PartialEqArray.eq
              core.cmp.PartialEqU8 top root
            .ok (level, next, some equal)
          else .ok (level, next, some false)
        else .ok (level, next, pending)
    else .ok (level, next, pending)
  else .ok (level, next, pending)

private noncomputable def sourceOddOneRootCheck
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (indices : Slice Std.U32) (levelSlice : Slice GeneratedDigest)
    (level next : GeneratedDigestVec) (nodePos : Std.Usize)
    (pending : Option Bool) : Result (ControlFlow RootLoopState RootOutput) := do
  if Slice.len indices = 1#usize then
    if Slice.len levelSlice = 1#usize then
      let index ← Slice.index_usize indices 0#usize
      let value ← Slice.index_usize levelSlice 0#usize
      let endPos := Std.Usize.wrapping_add nodePos 32#usize
      if endPos > Slice.len nodeBytes then .ok (.done (level, next, pending))
      else
        let siblingSlice ← core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) nodeBytes
          { start := nodePos, «end» := endPos }
        let copied ← core.array.TryFromArrayCopySlice.try_from 32#usize
          core.marker.CopyU8 siblingSlice
        let sibling ← core.result.Result.unwrap
          core.fmt.DebugTryFromSliceError copied
        if index = 0#u32 then
          let top ← merkle.fixed_node_hash value sibling
          if endPos = Slice.len nodeBytes then
            let equal ← core.array.equality.PartialEqArray.eq
              core.cmp.PartialEqU8 top root
            .ok (.done (level, next, some equal))
          else .ok (.done (level, next, some false))
        else if index = 1#u32 then
          let top ← merkle.fixed_node_hash sibling value
          if endPos = Slice.len nodeBytes then
            let equal ← core.array.equality.PartialEqArray.eq
              core.cmp.PartialEqU8 top root
            .ok (.done (level, next, some equal))
          else .ok (.done (level, next, some false))
        else .ok (.done (level, next, pending))
    else .ok (.done (level, next, pending))
  else .ok (.done (level, next, pending))

private theorem sourceOddOneRootCheck_eq_doneMap
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (indices : Slice Std.U32) (levelSlice : Slice GeneratedDigest)
    (level next : GeneratedDigestVec) (nodePos : Std.Usize)
    (pending : Option Bool) :
    sourceOddOneRootCheck root nodeBytes indices levelSlice level next nodePos
        pending =
      doneMap (rawOddOneRootCheck root nodeBytes indices levelSlice level next
        nodePos pending) := by
  unfold sourceOddOneRootCheck doneMap rawOddOneRootCheck
  by_cases hindicesLen : Slice.len indices = 1#usize
  · simp only [hindicesLen, if_true]
    by_cases hlevelLen : Slice.len levelSlice = 1#usize
    · simp only [hlevelLen, if_true]
      rw [Aeneas.Std.bind_assoc_eq]
      apply (Aeneas.Std.bind_eq_iff _ _ _).2
      intro index hindex
      rw [Aeneas.Std.bind_assoc_eq]
      apply (Aeneas.Std.bind_eq_iff _ _ _).2
      intro value hvalue
      by_cases hpast : Std.Usize.wrapping_add nodePos 32#usize >
          Slice.len nodeBytes
      · simp only [hpast, if_true]
        rfl
      · simp only [hpast, if_false]
        rw [Aeneas.Std.bind_assoc_eq]
        apply (Aeneas.Std.bind_eq_iff _ _ _).2
        intro siblingSlice hsiblingSlice
        rw [Aeneas.Std.bind_assoc_eq]
        apply (Aeneas.Std.bind_eq_iff _ _ _).2
        intro copied hcopied
        rw [Aeneas.Std.bind_assoc_eq]
        apply (Aeneas.Std.bind_eq_iff _ _ _).2
        intro sibling hsibling
        by_cases hleft : index = 0#u32
        · simp only [hleft, if_true]
          rw [Aeneas.Std.bind_assoc_eq]
          apply (Aeneas.Std.bind_eq_iff _ _ _).2
          intro top htop
          by_cases hcursor : Std.Usize.wrapping_add nodePos 32#usize =
              Slice.len nodeBytes
          · simp only [hcursor, if_true]
            rw [Aeneas.Std.bind_assoc_eq]
            apply (Aeneas.Std.bind_eq_iff _ _ _).2
            intro equal hequal
            rfl
          · simp only [hcursor, if_false]
            rfl
        · simp only [hleft, if_false]
          by_cases hright : index = 1#u32
          · simp only [hright, if_true]
            rw [Aeneas.Std.bind_assoc_eq]
            apply (Aeneas.Std.bind_eq_iff _ _ _).2
            intro top htop
            by_cases hcursor : Std.Usize.wrapping_add nodePos 32#usize =
                Slice.len nodeBytes
            · simp only [hcursor, if_true]
              rw [Aeneas.Std.bind_assoc_eq]
              apply (Aeneas.Std.bind_eq_iff _ _ _).2
              intro equal hequal
              rfl
            · simp only [hcursor, if_false]
              rfl
          · simp only [hright, if_false]
            rfl
    · simp only [hlevelLen, if_false]
      rfl
  · simp only [hindicesLen, if_false]
    rfl

private noncomputable def rawOddRootCheck
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (indices : Slice Std.U32) (level next : GeneratedDigestVec)
    (nodePos : Std.Usize) (pending : Option Bool) : Result RootOutput := do
  let levelSlice ← alloc.vec.Vec.as_slice Global level
  if Slice.len indices = 2#usize then
    rawOddTwoRootCheck root nodeBytes indices levelSlice level next nodePos
      pending
  else
    rawOddOneRootCheck root nodeBytes indices levelSlice level next nodePos
      pending

private noncomputable def sourceOddRootCheck
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (indices : Slice Std.U32) (level next : GeneratedDigestVec)
    (nodePos : Std.Usize) (pending : Option Bool) :
    Result (ControlFlow RootLoopState RootOutput) := do
  let levelSlice ← alloc.vec.Vec.as_slice Global level
  if Slice.len indices = 2#usize then
    sourceOddTwoRootCheck root nodeBytes indices levelSlice level next nodePos
      pending
  else
    sourceOddOneRootCheck root nodeBytes indices levelSlice level next nodePos
      pending

private theorem sourceOddRootCheck_eq_doneMap
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (indices : Slice Std.U32) (level next : GeneratedDigestVec)
    (nodePos : Std.Usize) (pending : Option Bool) :
    sourceOddRootCheck root nodeBytes indices level next nodePos pending =
      doneMap (rawOddRootCheck root nodeBytes indices level next nodePos
        pending) := by
  unfold sourceOddRootCheck doneMap rawOddRootCheck
  rw [Aeneas.Std.bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).2
  intro levelSlice hlevelSlice
  by_cases htwo : Slice.len indices = 2#usize
  · simp only [htwo, if_true]
    exact sourceOddTwoRootCheck_eq_doneMap root nodeBytes indices levelSlice
      level next nodePos pending
  · simp only [htwo, if_false]
    exact sourceOddOneRootCheck_eq_doneMap root nodeBytes indices levelSlice
      level next nodePos pending

noncomputable def rawFinalRootCheck
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (topology : merkle.Radix4BinaryCapTopology)
    (binaryDepth : Std.U32) (level next : GeneratedDigestVec)
    (nodePos : Std.Usize) (pending : Option Bool) :
    Result RootOutput := do
  let indices? ← merkle.Radix4BinaryCapTopology.impl.level_indices topology
    topology.radix_levels
  match indices? with
  | none => .ok (level, next, pending)
  | some indices =>
    if binaryDepth &&& 1#u32 = 0#u32 then
      rawEvenRootCheck root nodeBytes indices level next nodePos pending
    else
      rawOddRootCheck root nodeBytes indices level next nodePos pending

private noncomputable def sourceFinalRootCheck
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (topology : merkle.Radix4BinaryCapTopology)
    (binaryDepth : Std.U32) (level next : GeneratedDigestVec)
    (nodePos : Std.Usize) (pending : Option Bool) :
    Result (ControlFlow RootLoopState RootOutput) := do
  let indices? ← merkle.Radix4BinaryCapTopology.impl.level_indices topology
    topology.radix_levels
  match indices? with
  | none => .ok (.done (level, next, pending))
  | some indices =>
    if binaryDepth &&& 1#u32 = 0#u32 then
      sourceEvenRootCheck root nodeBytes indices level next nodePos pending
    else
      sourceOddRootCheck root nodeBytes indices level next nodePos pending

private theorem sourceFinalRootCheck_eq_doneMap
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (topology : merkle.Radix4BinaryCapTopology)
    (binaryDepth : Std.U32) (level next : GeneratedDigestVec)
    (nodePos : Std.Usize) (pending : Option Bool) :
    sourceFinalRootCheck root nodeBytes topology binaryDepth level next nodePos
        pending =
      doneMap (rawFinalRootCheck root nodeBytes topology binaryDepth level next
        nodePos pending) := by
  unfold sourceFinalRootCheck doneMap rawFinalRootCheck
  rw [Aeneas.Std.bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).2
  intro indicesOption hindices
  cases indicesOption with
  | none => rfl
  | some indices =>
      by_cases heven : binaryDepth &&& 1#u32 = 0#u32
      · simp only [heven, if_true]
        exact sourceEvenRootCheck_eq_doneMap root nodeBytes indices level next
          nodePos pending
      · simp only [heven, if_false]
        exact sourceOddRootCheck_eq_doneMap root nodeBytes indices level next
          nodePos pending

private theorem unchanged_terminal_body_eq_sourceFinalRootCheck
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (topology : merkle.Radix4BinaryCapTopology)
    (binaryDepth : Std.U32) (iter : core.ops.range.Range Std.Usize)
    (level next : GeneratedDigestVec) (nodePos : Std.Usize)
    (pending : Option Bool)
    (hnext : core.iter.range.IteratorRange.next
      core.iter.range.StepUsize iter = .ok (none, iter)) :
    merkle.verify_radix4_binary_cap_with_matched_topology_loop0.body root
        nodeBytes topology.binary_depth topology.radix_levels
        topology.level_indices topology.level_offsets topology.group_masks
        topology.group_offsets binaryDepth iter level next nodePos pending =
      sourceFinalRootCheck root nodeBytes topology binaryDepth level next
        nodePos pending := by
  unfold
    merkle.verify_radix4_binary_cap_with_matched_topology_loop0.body
    sourceFinalRootCheck sourceEvenRootCheck sourceOddRootCheck
    sourceOddTwoRootCheck sourceOddOneRootCheck
  simp only [hnext, Aeneas.Std.bind_tc_ok, lift]
  rfl

theorem raw_final_root_check_success_yields_witness
    (sha256 : List ModelByte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (topology : merkle.Radix4BinaryCapTopology)
    (binaryDepth : Std.U32) (iter : core.ops.range.Range Std.Usize)
    (level next : GeneratedDigestVec)
    (nodePos : Std.Usize) (finalLevel finalNext : GeneratedDigestVec)
    (hnext : core.iter.range.IteratorRange.next
      core.iter.range.StepUsize iter = .ok (none, iter))
    (hrun :
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0 iter root
        nodeBytes topology.binary_depth topology.radix_levels
        topology.level_indices topology.level_offsets topology.group_masks
        topology.group_offsets binaryDepth level next nodePos none =
      .ok (finalLevel, finalNext, some true)) :
    finalLevel = level ∧ finalNext = next ∧
      Nonempty (RawFinalRootWitness sha256 root nodeBytes topology binaryDepth
        level nodePos) := by
  have hloop_eq_raw :
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0 iter root
          nodeBytes topology.binary_depth topology.radix_levels
          topology.level_indices topology.level_offsets topology.group_masks
          topology.group_offsets binaryDepth level next nodePos none =
        rawFinalRootCheck root nodeBytes topology binaryDepth level next
          nodePos none := by
    unfold merkle.verify_radix4_binary_cap_with_matched_topology_loop0
    rw [Aeneas.Std.loop.eq_def]
    simp only
    rw [unchanged_terminal_body_eq_sourceFinalRootCheck root nodeBytes
      topology binaryDepth iter level next nodePos none hnext]
    rw [sourceFinalRootCheck_eq_doneMap]
    unfold doneMap
    cases hraw : rawFinalRootCheck root nodeBytes topology binaryDepth level
      next nodePos none <;> simp [hraw, Bind.bind, Aeneas.Std.bind]
  rw [hloop_eq_raw] at hrun
  unfold rawFinalRootCheck rawEvenRootCheck rawOddRootCheck
    rawOddTwoRootCheck rawOddOneRootCheck at hrun
  generalize hindices :
    merkle.Radix4BinaryCapTopology.impl.level_indices topology
      topology.radix_levels = indicesResult at hrun
  cases indicesResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok indicesOption =>
      simp only [Aeneas.Std.bind_tc_ok] at hrun
      cases indicesOption with
      | none => simp at hrun
      | some indices =>
          simp only at hrun
          by_cases heven : binaryDepth &&& 1#u32 = 0#u32
          · rw [if_pos heven] at hrun
            generalize hlevelSlice :
              alloc.vec.Vec.as_slice Global level = levelSliceResult at hrun
            cases levelSliceResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | ok levelSlice =>
                simp only [Aeneas.Std.bind_tc_ok] at hrun
                by_cases hone : Slice.len indices = 1#usize
                · rw [if_pos hone] at hrun
                  by_cases hlevelOne : Slice.len levelSlice = 1#usize
                  · rw [if_pos hlevelOne] at hrun
                    generalize hindex : Slice.index_usize indices 0#usize =
                      indexResult at hrun
                    cases indexResult with
                    | fail error =>
                        simp [Bind.bind, Aeneas.Std.bind] at hrun
                    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                    | ok index =>
                        simp only [Aeneas.Std.bind_tc_ok] at hrun
                        split at hrun
                        next hindexZero =>
                          generalize hvalue :
                            Slice.index_usize levelSlice 0#usize =
                              valueResult at hrun
                          cases valueResult with
                          | fail error =>
                              simp [Bind.bind, Aeneas.Std.bind] at hrun
                          | div =>
                              simp [Bind.bind, Aeneas.Std.bind] at hrun
                          | ok value =>
                              simp only [Aeneas.Std.bind_tc_ok] at hrun
                              by_cases hcursor :
                                  nodePos = Slice.len nodeBytes
                              · rw [if_pos hcursor] at hrun
                                generalize hcompare :
                                  core.array.equality.PartialEqArray.eq
                                      core.cmp.PartialEqU8 value root =
                                    compareResult at hrun
                                cases compareResult with
                                | fail error =>
                                    simp [Bind.bind, Aeneas.Std.bind] at hrun
                                | div =>
                                    simp [Bind.bind, Aeneas.Std.bind] at hrun
                                | ok equal =>
                                    have hout := Result.ok.inj hrun
                                    have hlevelOut : level = finalLevel :=
                                      congrArg (fun output => output.1) hout
                                    have hnextOut : next = finalNext :=
                                      congrArg (fun output => output.2.1) hout
                                    have hequal : equal = true :=
                                      Option.some.inj (congrArg
                                        (fun output => output.2.2) hout)
                                    subst finalLevel
                                    subst finalNext
                                    subst equal
                                    exact ⟨rfl, rfl,
                                      ⟨RawFinalRootWitness.even indices
                                        levelSlice value hindices heven
                                        hlevelSlice hone hlevelOne
                                        (by
                                          rw [zero_pattern_eq_zero_u32] at hindex
                                          exact hindex)
                                        hvalue hcursor
                                        (congrArg generatedArrayToDigest
                                          (generated_digest_eq_true_implies_eq
                                            value root hcompare))⟩⟩
                              · rw [if_neg hcursor] at hrun
                                simp at hrun
                        next hindexOther => simp at hrun
                  · rw [if_neg hlevelOne] at hrun
                    simp at hrun
                · rw [if_neg hone] at hrun
                  simp at hrun
          · rw [if_neg heven] at hrun
            generalize hlevelSlice :
              alloc.vec.Vec.as_slice Global level = levelSliceResult at hrun
            cases levelSliceResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | ok levelSlice =>
                simp only [Aeneas.Std.bind_tc_ok] at hrun
                by_cases htwo : Slice.len indices = 2#usize
                · rw [if_pos htwo] at hrun
                  by_cases hlevelTwo : Slice.len levelSlice = 2#usize
                  · rw [if_pos hlevelTwo] at hrun
                    generalize hfirst :
                      Slice.index_usize indices 0#usize = firstResult at hrun
                    cases firstResult with
                    | fail error =>
                        simp [Bind.bind, Aeneas.Std.bind] at hrun
                    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                    | ok first =>
                        simp only [Aeneas.Std.bind_tc_ok] at hrun
                        split at hrun
                        next hfirstZero =>
                          generalize hsecond :
                            Slice.index_usize indices 1#usize =
                              secondResult at hrun
                          cases secondResult with
                          | fail error =>
                              simp [Bind.bind, Aeneas.Std.bind] at hrun
                          | div =>
                              simp [Bind.bind, Aeneas.Std.bind] at hrun
                          | ok second =>
                              simp only [Aeneas.Std.bind_tc_ok] at hrun
                              split at hrun
                              next hsecondOne =>
                                generalize hleft :
                                  Slice.index_usize levelSlice 0#usize =
                                    leftResult at hrun
                                cases leftResult with
                                | fail error =>
                                    simp [Bind.bind, Aeneas.Std.bind] at hrun
                                | div =>
                                    simp [Bind.bind, Aeneas.Std.bind] at hrun
                                | ok left =>
                                  simp only [Aeneas.Std.bind_tc_ok] at hrun
                                  generalize hright :
                                    Slice.index_usize levelSlice 1#usize =
                                      rightResult at hrun
                                  cases rightResult with
                                  | fail error =>
                                      simp [Bind.bind, Aeneas.Std.bind] at hrun
                                  | div =>
                                      simp [Bind.bind, Aeneas.Std.bind] at hrun
                                  | ok right =>
                                    simp only [Aeneas.Std.bind_tc_ok] at hrun
                                    generalize hnode :
                                      merkle.fixed_node_hash left right =
                                        nodeResult at hrun
                                    cases nodeResult with
                                    | fail error =>
                                        simp [Bind.bind, Aeneas.Std.bind]
                                          at hrun
                                    | div =>
                                        simp [Bind.bind, Aeneas.Std.bind]
                                          at hrun
                                    | ok top =>
                                      simp only [Aeneas.Std.bind_tc_ok] at hrun
                                      by_cases hcursor :
                                          nodePos = Slice.len nodeBytes
                                      · rw [if_pos hcursor] at hrun
                                        generalize hcompare :
                                          core.array.equality.PartialEqArray.eq
                                              core.cmp.PartialEqU8 top root =
                                            compareResult at hrun
                                        cases compareResult with
                                        | fail error =>
                                            simp [Bind.bind, Aeneas.Std.bind]
                                              at hrun
                                        | div =>
                                            simp [Bind.bind, Aeneas.Std.bind]
                                              at hrun
                                        | ok equal =>
                                          have hout := Result.ok.inj hrun
                                          have hlevelOut : level = finalLevel :=
                                            congrArg (fun output => output.1)
                                              hout
                                          have hnextOut : next = finalNext :=
                                            congrArg (fun output => output.2.1)
                                              hout
                                          have hequal : equal = true :=
                                            Option.some.inj (congrArg
                                              (fun output => output.2.2) hout)
                                          subst finalLevel
                                          subst finalNext
                                          subst equal
                                          exact ⟨rfl, rfl,
                                            ⟨RawFinalRootWitness.odd
                                              indices left right hindices heven
                                              (RawOddCapLocation.both levelSlice
                                                left right hlevelSlice htwo
                                                hlevelTwo
                                                (by
                                                  rw [zero_pattern_eq_zero_u32]
                                                    at hfirst
                                                  exact hfirst)
                                                (by
                                                  rw [one_pattern_eq_one_u32]
                                                    at hsecond
                                                  exact hsecond)
                                                hleft hright hcursor)
                                              (fixed_node_hash_and_compare_exact
                                                sha256 hhash left right top root
                                                hnode hcompare)⟩⟩
                                      · rw [if_neg hcursor] at hrun
                                        simp at hrun
                              next hsecondOther => simp at hrun
                        next hfirstOther => simp at hrun
                  · rw [if_neg hlevelTwo] at hrun
                    simp at hrun
                · rw [if_neg htwo] at hrun
                  by_cases hone : Slice.len indices = 1#usize
                  · rw [if_pos hone] at hrun
                    by_cases hlevelOne : Slice.len levelSlice = 1#usize
                    · rw [if_pos hlevelOne] at hrun
                      generalize hindex :
                        Slice.index_usize indices 0#usize = indexResult at hrun
                      cases indexResult with
                      | fail error =>
                          simp [Bind.bind, Aeneas.Std.bind] at hrun
                      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                      | ok index =>
                        simp only [Aeneas.Std.bind_tc_ok] at hrun
                        generalize hvalue :
                          Slice.index_usize levelSlice 0#usize =
                            valueResult at hrun
                        cases valueResult with
                        | fail error =>
                            simp [Bind.bind, Aeneas.Std.bind] at hrun
                        | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                        | ok value =>
                          simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
                          by_cases hpast :
                              Std.Usize.wrapping_add nodePos 32#usize >
                                Slice.len nodeBytes
                          · rw [if_pos hpast] at hrun
                            simp at hrun
                          · rw [if_neg hpast] at hrun
                            generalize hsiblingSlice :
                              core.slice.index.Slice.index
                                  (core.slice.index.SliceIndexRangeUsizeSlice
                                    Std.U8)
                                  nodeBytes
                                  { start := nodePos,
                                    «end» := Std.Usize.wrapping_add nodePos
                                      32#usize } =
                                siblingSliceResult at hrun
                            cases siblingSliceResult with
                            | fail error =>
                                simp [Bind.bind, Aeneas.Std.bind] at hrun
                            | div =>
                                simp [Bind.bind, Aeneas.Std.bind] at hrun
                            | ok siblingSlice =>
                              simp only [Aeneas.Std.bind_tc_ok] at hrun
                              generalize hcopy :
                                core.array.TryFromArrayCopySlice.try_from
                                    32#usize core.marker.CopyU8 siblingSlice =
                                  copyResult at hrun
                              cases copyResult with
                              | fail error =>
                                  simp [Bind.bind, Aeneas.Std.bind] at hrun
                              | div =>
                                  simp [Bind.bind, Aeneas.Std.bind] at hrun
                              | ok copied =>
                                simp only [Aeneas.Std.bind_tc_ok] at hrun
                                cases copied with
                                | Err error =>
                                  simp [core.result.Result.unwrap, Bind.bind,
                                    Aeneas.Std.bind] at hrun
                                | Ok sibling =>
                                  simp only [core.result.Result.unwrap,
                                    Aeneas.Std.bind_tc_ok, lift] at hrun
                                  by_cases hleftSide : index = 0#u32
                                  · rw [if_pos hleftSide] at hrun
                                    generalize hnode :
                                      merkle.fixed_node_hash value sibling =
                                        nodeResult at hrun
                                    cases nodeResult with
                                    | fail error =>
                                        simp [Bind.bind, Aeneas.Std.bind]
                                          at hrun
                                    | div =>
                                        simp [Bind.bind, Aeneas.Std.bind]
                                          at hrun
                                    | ok top =>
                                      simp only [Aeneas.Std.bind_tc_ok] at hrun
                                      by_cases hcursor :
                                          Std.Usize.wrapping_add nodePos
                                              32#usize = Slice.len nodeBytes
                                      · rw [if_pos hcursor] at hrun
                                        generalize hcompare :
                                          core.array.equality.PartialEqArray.eq
                                              core.cmp.PartialEqU8 top root =
                                            compareResult at hrun
                                        cases compareResult with
                                        | fail error =>
                                            simp [Bind.bind, Aeneas.Std.bind]
                                              at hrun
                                        | div =>
                                            simp [Bind.bind, Aeneas.Std.bind]
                                              at hrun
                                        | ok equal =>
                                          have hout := Result.ok.inj hrun
                                          have hlevelOut : level = finalLevel :=
                                            congrArg (fun output => output.1)
                                              hout
                                          have hnextOut : next = finalNext :=
                                            congrArg (fun output => output.2.1)
                                              hout
                                          have hequal : equal = true :=
                                            Option.some.inj (congrArg
                                              (fun output => output.2.2) hout)
                                          subst finalLevel
                                          subst finalNext
                                          subst equal
                                          exact ⟨rfl, rfl,
                                            ⟨RawFinalRootWitness.odd
                                              indices value sibling hindices
                                              heven
                                              (RawOddCapLocation.liveLeft
                                                levelSlice value sibling
                                                siblingSlice hlevelSlice hone
                                                hlevelOne
                                                (by simpa [hleftSide] using
                                                  hindex)
                                                hvalue hsiblingSlice hcopy
                                                hcursor)
                                              (fixed_node_hash_and_compare_exact
                                                sha256 hhash value sibling top
                                                root hnode hcompare)⟩⟩
                                      · rw [if_neg hcursor] at hrun
                                        simp at hrun
                                  · rw [if_neg hleftSide] at hrun
                                    by_cases hrightSide : index = 1#u32
                                    · rw [if_pos hrightSide] at hrun
                                      generalize hnode :
                                        merkle.fixed_node_hash sibling value =
                                          nodeResult at hrun
                                      cases nodeResult with
                                      | fail error =>
                                          simp [Bind.bind, Aeneas.Std.bind]
                                            at hrun
                                      | div =>
                                          simp [Bind.bind, Aeneas.Std.bind]
                                            at hrun
                                      | ok top =>
                                        simp only [Aeneas.Std.bind_tc_ok]
                                          at hrun
                                        by_cases hcursor :
                                            Std.Usize.wrapping_add nodePos
                                                32#usize = Slice.len nodeBytes
                                        · rw [if_pos hcursor] at hrun
                                          generalize hcompare :
                                            core.array.equality.PartialEqArray.eq
                                                core.cmp.PartialEqU8 top root =
                                              compareResult at hrun
                                          cases compareResult with
                                          | fail error =>
                                              simp [Bind.bind, Aeneas.Std.bind]
                                                at hrun
                                          | div =>
                                              simp [Bind.bind, Aeneas.Std.bind]
                                                at hrun
                                          | ok equal =>
                                            have hout := Result.ok.inj hrun
                                            have hlevelOut :
                                                level = finalLevel :=
                                              congrArg
                                                (fun output => output.1) hout
                                            have hnextOut : next = finalNext :=
                                              congrArg
                                                (fun output => output.2.1) hout
                                            have hequal : equal = true :=
                                              Option.some.inj (congrArg
                                                (fun output => output.2.2)
                                                hout)
                                            subst finalLevel
                                            subst finalNext
                                            subst equal
                                            exact ⟨rfl, rfl,
                                              ⟨RawFinalRootWitness.odd
                                                indices sibling value hindices
                                                heven
                                                (RawOddCapLocation.liveRight
                                                  levelSlice value sibling
                                                  siblingSlice hlevelSlice hone
                                                  hlevelOne
                                                  (by simpa [hrightSide] using
                                                    hindex)
                                                  hvalue hsiblingSlice hcopy
                                                  hcursor)
                                                (fixed_node_hash_and_compare_exact
                                                  sha256 hhash sibling value top
                                                  root hnode hcompare)⟩⟩
                                        · rw [if_neg hcursor] at hrun
                                          simp at hrun
                                    · rw [if_neg hrightSide] at hrun
                                      simp at hrun
                    · rw [if_neg hlevelOne] at hrun
                      simp at hrun
                  · rw [if_neg hone] at hrun
                    simp at hrun

/-! ## The unchanged topology-level loop -/

/-- Complete exact trace of the unchanged outer loop.  Every `step` records
the literal topology mask slice, the scratch clear, the complete group trace,
and the next range state.  `done` records the exact accepted root check. -/
inductive RawLevelTrace
    (sha256 : List ModelByte → Digest32)
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (topology : merkle.Radix4BinaryCapTopology)
    (binaryDepth : Std.U32) :
    core.ops.range.Range Std.Usize → GeneratedDigestVec → GeneratedDigestVec →
      Std.Usize → Option Bool → GeneratedDigestVec → GeneratedDigestVec → Prop
  | done (iter : core.ops.range.Range Std.Usize)
      (level next : GeneratedDigestVec) (nodePos : Std.Usize)
      (pending : Option Bool)
      (iterator_finished : iter.end.val ≤ iter.start.val)
      (pending_none : pending = none)
      (root_check : RawFinalRootWitness sha256 root nodeBytes topology
        binaryDepth level nodePos) :
      RawLevelTrace sha256 root nodeBytes topology binaryDepth iter level next
        nodePos pending level next
  | step (iter iter' : core.ops.range.Range Std.Usize)
      (planLevel : Std.Usize)
      (level next nextCleared level' next' finalLevel finalNext :
        GeneratedDigestVec)
      (nodePos nodePos' : Std.Usize) (pending pending' : Option Bool)
      (masks : Slice Std.U8) (maskIter : core.slice.iter.Iter Std.U8)
      (iterator_next : core.iter.range.IteratorRange.next
        core.iter.range.StepUsize iter = .ok (some planLevel, iter'))
      (clear_run : alloc.vec.Vec.clear Global next = .ok nextCleared)
      (masks_run : merkle.Radix4BinaryCapTopology.impl.group_masks topology
        planLevel = .ok (some masks))
      (mask_iterator_run :
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
          masks = .ok maskIter)
      (groups_run :
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0
          maskIter nodeBytes level nextCleared nodePos 0#usize pending =
        .ok (level', next', nodePos', pending', 1#u32))
      (groups : RawGroupTrace sha256 nodeBytes level maskIter nextCleared
        nodePos 0#usize pending level' next' nodePos' pending')
      (tail : RawLevelTrace sha256 root nodeBytes topology binaryDepth iter'
        level' next' nodePos' pending' finalLevel finalNext) :
      RawLevelTrace sha256 root nodeBytes topology binaryDepth iter level next
        nodePos pending finalLevel finalNext

private theorem raw_level_loop_from_span
    (sha256 : List ModelByte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (topology : merkle.Radix4BinaryCapTopology)
    (binaryDepth : Std.U32) (remaining : Nat)
    (iter : core.ops.range.Range Std.Usize)
    (level next finalLevel finalNext : GeneratedDigestVec)
    (nodePos : Std.Usize) (pending : Option Bool)
    (hspan : remaining = iter.end.val - iter.start.val)
    (hend : iter.end = topology.radix_levels)
    (hpending : pending = none)
    (hnodeLe : nodePos.val ≤ nodeBytes.val.length)
    (hroom : nodeBytes.val.length + 32 < UScalar.size .Usize)
    (hrun :
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0 iter root
        nodeBytes topology.binary_depth topology.radix_levels
        topology.level_indices topology.level_offsets topology.group_masks
        topology.group_offsets binaryDepth level next nodePos pending =
      .ok (finalLevel, finalNext, some true)) :
    Nonempty (RawLevelTrace sha256 root nodeBytes topology binaryDepth iter
      level next nodePos pending finalLevel finalNext) := by
  induction remaining generalizing iter level next nodePos pending with
  | zero =>
      have hfinished : iter.end.val ≤ iter.start.val := by omega
      have hs := core.iter.range.IteratorRange.next_Usize_none_spec iter
        hfinished
      rcases Aeneas.Std.WP.spec_imp_exists hs with
        ⟨⟨option, iter'⟩, hnext, hoption, hiter⟩
      rw [hoption, hiter] at hnext
      subst pending
      obtain ⟨hfinalLevel, hfinalNext, ⟨rootCheck⟩⟩ :=
        raw_final_root_check_success_yields_witness sha256 hhash root
          nodeBytes topology binaryDepth iter level next nodePos finalLevel
          finalNext hnext hrun
      subst finalLevel
      subst finalNext
      exact ⟨RawLevelTrace.done iter level next nodePos none hfinished rfl
        rootCheck⟩
  | succ remaining ih =>
      have hactive : iter.start.val < iter.end.val := by omega
      have hs := core.iter.range.IteratorRange.next_Usize_some_spec iter hactive
      rcases Aeneas.Std.WP.spec_imp_exists hs with
        ⟨⟨option, iter'⟩, hnext, hoption, hiterStart, hiterEnd⟩
      rw [hoption] at hnext
      unfold
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0 at hrun
      rw [Aeneas.Std.loop.eq_def] at hrun
      simp only at hrun
      generalize hbody :
        merkle.verify_radix4_binary_cap_with_matched_topology_loop0.body root
          nodeBytes topology.binary_depth topology.radix_levels
          topology.level_indices topology.level_offsets topology.group_masks
          topology.group_offsets binaryDepth iter level next nodePos pending =
            bodyResult at hrun
      cases bodyResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok flow =>
        unfold
          merkle.verify_radix4_binary_cap_with_matched_topology_loop0.body at hbody
        simp only [hnext, Aeneas.Std.bind_tc_ok, lift] at hbody
        generalize hclear : alloc.vec.Vec.clear Global next = clearResult at hbody
        cases clearResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at hbody
        | div => simp [Bind.bind, Aeneas.Std.bind] at hbody
        | ok nextCleared =>
            simp only [Aeneas.Std.bind_tc_ok] at hbody
            generalize hmasks :
              merkle.Radix4BinaryCapTopology.impl.group_masks topology
                iter.start = masksResult at hbody
            cases masksResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hbody
            | div => simp [Bind.bind, Aeneas.Std.bind] at hbody
            | ok masksOption =>
                simp only [Aeneas.Std.bind_tc_ok] at hbody
                cases masksOption with
                | none =>
                    have hflow := (Result.ok.inj hbody).symm
                    subst flow
                    simp at hrun
                | some masks =>
                    generalize hmaskIter :
                      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
                        masks = maskIterResult at hbody
                    cases maskIterResult with
                    | fail error =>
                        simp [hmaskIter, Bind.bind, Aeneas.Std.bind] at hbody
                    | div =>
                        simp [hmaskIter, Bind.bind, Aeneas.Std.bind] at hbody
                    | ok maskIter =>
                        simp only [hmaskIter, Aeneas.Std.bind_tc_ok] at hbody
                        generalize hgroups :
                          merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0
                            maskIter nodeBytes level nextCleared nodePos 0#usize
                            pending = groupsResult at hbody
                        cases groupsResult with
                        | fail error =>
                            simp [hgroups, Bind.bind, Aeneas.Std.bind] at hbody
                        | div =>
                            simp [hgroups, Bind.bind, Aeneas.Std.bind] at hbody
                        | ok groupsOutput =>
                            rcases groupsOutput with
                              ⟨level', next', nodePos', pending', code⟩
                            simp only [hgroups, Aeneas.Std.bind_tc_ok] at hbody
                            have hpendingNot : pending' ≠ some true :=
                              group_loop_preserves_not_true_from_span
                                (maskIter.slice.val.length - maskIter.i)
                                maskIter nodeBytes level nextCleared level' next'
                                nodePos 0#usize nodePos' pending pending' code rfl
                                (by rw [hpending]; simp) hgroups
                            split at hbody
                            next codeOne =>
                              have hflow : flow = ControlFlow.cont
                                  (iter', level', next', nodePos', pending') :=
                                (Result.ok.inj hbody).symm
                              subst flow
                              simp only at hrun
                              have hgroupsOne :
                                  merkle.verify_radix4_binary_cap_with_matched_topology_loop0_loop0
                                      maskIter nodeBytes level nextCleared nodePos
                                      0#usize pending =
                                    .ok (level', next', nodePos', pending',
                                      1#u32) := by
                                rw [one_pattern_eq_one_u32] at hgroups
                                exact hgroups
                              let groups := Classical.choice
                                (unchanged_group_loop_success_yields_trace
                                  sha256 hhash maskIter nodeBytes level
                                  nextCleared nodePos 0#usize pending level' next'
                                  nodePos' pending' hnodeLe hroom hgroupsOne)
                              have hpending' : pending' = none :=
                                groups.finalPending_eq.trans hpending
                              have hnextNode :
                                  nodePos'.val ≤ nodeBytes.val.length :=
                                groups.finalNodePos_le hnodeLe
                              have hspan' : remaining =
                                  iter'.end.val - iter'.start.val := by
                                rw [hiterStart, hiterEnd]
                                omega
                              have hend' : iter'.end = topology.radix_levels := by
                                rw [hiterEnd]
                                exact hend
                              change
                                merkle.verify_radix4_binary_cap_with_matched_topology_loop0
                                  iter' root nodeBytes topology.binary_depth
                                  topology.radix_levels topology.level_indices
                                  topology.level_offsets topology.group_masks
                                  topology.group_offsets binaryDepth level' next'
                                  nodePos' pending' =
                                .ok (finalLevel, finalNext, some true) at hrun
                              let tail := Classical.choice
                                (ih iter' level' next' nodePos' pending' hspan'
                                  hend' hpending' hnextNode hrun)
                              exact ⟨RawLevelTrace.step iter iter' iter.start
                                level next nextCleared level' next' finalLevel
                                finalNext nodePos nodePos' pending pending' masks
                                maskIter hnext hclear hmasks hmaskIter hgroupsOne
                                groups tail⟩
                            next codeOther =>
                              cases pending' with
                              | none =>
                                  have hflow := (Result.ok.inj hbody).symm
                                  subst flow
                                  simp at hrun
                              | some accepted =>
                                  have hflow := (Result.ok.inj hbody).symm
                                  subst flow
                                  simp only at hrun
                                  have haccepted : accepted = true := by
                                    exact Option.some.inj (congrArg
                                      (fun output => output.2.2)
                                      (Result.ok.inj hrun))
                                  subst accepted
                                  exact False.elim (hpendingNot rfl)

/-- The complete unchanged outer loop, from any exact range suffix, yields a
nested level/group/child trace and the maintained final root equation. -/
theorem unchanged_level_loop_success_yields_trace
    (sha256 : List ModelByte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (topology : merkle.Radix4BinaryCapTopology)
    (binaryDepth : Std.U32) (iter : core.ops.range.Range Std.Usize)
    (level next finalLevel finalNext : GeneratedDigestVec)
    (nodePos : Std.Usize)
    (hend : iter.end = topology.radix_levels)
    (hnodeLe : nodePos.val ≤ nodeBytes.val.length)
    (hroom : nodeBytes.val.length + 32 < UScalar.size .Usize)
    (hrun :
      merkle.verify_radix4_binary_cap_with_matched_topology_loop0 iter root
        nodeBytes topology.binary_depth topology.radix_levels
        topology.level_indices topology.level_offsets topology.group_masks
        topology.group_offsets binaryDepth level next nodePos none =
      .ok (finalLevel, finalNext, some true)) :
    Nonempty (RawLevelTrace sha256 root nodeBytes topology binaryDepth iter
      level next nodePos none finalLevel finalNext) := by
  apply raw_level_loop_from_span sha256 hhash root nodeBytes topology
    binaryDepth (iter.end.val - iter.start.val) iter level next finalLevel
    finalNext nodePos none
  · rfl
  · exact hend
  · rfl
  · exact hnodeLe
  · exact hroom
  · exact hrun

/-- End-to-end theorem for the unchanged generated authentication function.
Every accepted call yields the nested source trace, every exact radix-four
SHA-256 equation, exact frontier consumption, and the final maintained-model
root comparison. -/
theorem accepted_unchanged_radix_yields_full_trace
    (sha256 : List ModelByte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (root : GeneratedDigest) (nodeBytes : Slice Std.U8)
    (matched : merkle.MatchedRadix4BinaryCapSuffix)
    (level next outputLevel outputNext : GeneratedDigestVec)
    (hroom : nodeBytes.val.length + 32 < UScalar.size .Usize)
    (hrun : merkle.verify_radix4_binary_cap_with_matched_topology root
      nodeBytes matched level next = .ok (true, outputLevel, outputNext)) :
    Nonempty (RawLevelTrace sha256 root nodeBytes matched.topology
      matched.binary_depth
      { start := matched.radix_level,
        «end» := matched.topology.radix_levels }
      level next 0#usize none outputLevel outputNext) := by
  let execution :=
    AspisV5MerkleUntouchedRadixInversion.accepted_radix_execution root
      nodeBytes matched level next outputLevel outputNext hrun
  exact unchanged_level_loop_success_yields_trace sha256 hhash root nodeBytes
    matched.topology matched.binary_depth
    { start := matched.radix_level,
      «end» := matched.topology.radix_levels }
    level next outputLevel outputNext 0#usize rfl (by norm_num) hroom
    execution.loop_run

#print axioms fixed_node_hash_exact
#print axioms raw_radix_hash_exact
#print axioms rawWriteChildSlice_exact
#print axioms filledChildPrefix_append
#print axioms input_eq_rawRadixPreimage_of_filled_four
#print axioms usize_succ_val
#print axioms usize_add_32_val
#print axioms raw_child_loop_from_prefix
#print axioms unchanged_four_child_loop_success_yields_witness
#print axioms child_loop_preserves_not_true_from_span
#print axioms group_loop_preserves_not_true_from_span
#print axioms raw_final_root_check_success_yields_witness
#print axioms unchanged_level_loop_success_yields_trace
#print axioms accepted_unchanged_radix_yields_full_trace

end AspisV5MerkleUntouchedRadixSoundness
