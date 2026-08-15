import V5MerkleDeployedSource.Funs
import V5MerkleGeneratedHelperBridge

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleGeneratedRadixBridge

open V5MerkleDeployedSource
open AspisV5MerkleGeneratedHelperBridge
open AspisV5MerkleRustBridge

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedRadixInput := Array Std.U8 129#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest

def radixInputByte (input : GeneratedRadixInput) (slot byte : Nat) : Std.U8 :=
  input.val[1 + slot * 32 + byte]!

def generatedDigestByte (digest : GeneratedDigest) (byte : Nat) : Std.U8 :=
  digest.val[byte]!

private theorem fixed_write_index_val
    (slot byte : Std.Usize) (hslot : slot.val < 4)
    (hbyte : byte.val < 32) :
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_add 1#usize
        (Std.Usize.wrapping_mul slot 32#usize)) byte).val =
      1 + slot.val * 32 + byte.val := by
  have hsize : 130 < UScalar.size .Usize := by
    have h := (130#usize).hSize
    simpa using h
  have hsizes : UScalar.size .Usize = Usize.size :=
    UScalar.size_UScalarTyUsize
  have hmul : (Std.Usize.wrapping_mul slot 32#usize).val =
      slot.val * 32 := by
    rw [Std.Usize.wrapping_mul_val_eq]
    apply Nat.mod_eq_of_lt
    norm_num
    rw [← hsizes]
    omega
  have hadd : (Std.Usize.wrapping_add 1#usize
      (Std.Usize.wrapping_mul slot 32#usize)).val =
      1 + slot.val * 32 := by
    rw [Std.Usize.wrapping_add_val_eq, hmul]
    norm_num
    apply Nat.mod_eq_of_lt
    rw [← hsizes]
    omega
  rw [Std.Usize.wrapping_add_val_eq, hadd]
  apply Nat.mod_eq_of_lt
  omega

private theorem fixed_write_next_byte_val
    (byte : Std.Usize) (hbyte : byte.val < 32) :
    (Std.Usize.wrapping_add byte 1#usize).val = byte.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  apply Nat.mod_eq_of_lt
  have hsize : 34 < UScalar.size .Usize := by
    have h := (34#usize).hSize
    simpa using h
  rw [← UScalar.size_UScalarTyUsize]
  omega

private def FixedWriteInvariant (slot : Std.Usize)
    (child : GeneratedDigest)
    (state : GeneratedRadixInput × Std.Usize) : Prop :=
  state.2.val ≤ 32 ∧
    ∀ byte, byte < state.2.val →
      radixInputByte state.1 slot.val byte = generatedDigestByte child byte

private def FixedWritePost (slot : Std.Usize) (child : GeneratedDigest)
    (output : GeneratedRadixInput) : Prop :=
  ∀ byte, byte < 32 →
    radixInputByte output slot.val byte = generatedDigestByte child byte

private theorem fixed_read_index_val
    (nodeBytes : Slice Std.U8) (nodePos byte : Std.Usize)
    (hspace : nodePos.val + 32 ≤ nodeBytes.val.length)
    (hbyte : byte.val < 32) :
    (Std.Usize.wrapping_add nodePos byte).val =
      nodePos.val + byte.val := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hsizes : UScalar.size .Usize = Usize.size :=
    UScalar.size_UScalarTyUsize
  have hmax : Usize.max < Usize.size := by
    rcases System.Platform.numBits_eq with hbits | hbits <;>
      simp [Usize.max, Usize.size, Usize.numBits, hbits]
  have hsize : nodeBytes.val.length < UScalar.size .Usize := by
    have hlength := nodeBytes.property
    rw [hsizes]
    omega
  omega

private def FixedReadInvariant (nodeBytes : Slice Std.U8)
    (nodePos : Std.Usize) (state : GeneratedDigest × Std.Usize) : Prop :=
  state.2.val ≤ 32 ∧
    ∀ byte, byte < state.2.val →
      generatedDigestByte state.1 byte =
        nodeBytes.val[nodePos.val + byte]!

private def FixedReadPost (nodeBytes : Slice Std.U8)
    (nodePos : Std.Usize) (output : GeneratedDigest) : Prop :=
  ∀ byte, byte < 32 →
    generatedDigestByte output byte =
      nodeBytes.val[nodePos.val + byte]!

/-- The generated fixed-size copy loop really writes all 32 child bytes into
the selected radix-four slot.  This closes the byte-copy part of the hash
preimage rather than treating the generated helper as an oracle. -/
theorem fixed_write_radix_child_exact
    (input output : GeneratedRadixInput) (slot : Std.Usize)
    (child : GeneratedDigest) (hslot : slot.val < 4)
    (hrun : merkle.fixed_write_radix_child input slot child = .ok output) :
    ∀ byte, byte < 32 →
      radixInputByte output slot.val byte = generatedDigestByte child byte := by
  have hspec :
      merkle.fixed_write_radix_child_loop input slot child 0#usize
        ⦃ out => FixedWritePost slot child out ⦄ := by
    simp only [merkle.fixed_write_radix_child_loop]
    apply Aeneas.Std.loop.spec_decr_nat
      (fun state : GeneratedRadixInput × Std.Usize => 32 - state.2.val)
      (FixedWriteInvariant slot child)
      (FixedWritePost slot child)
    · rintro ⟨current, currentByte⟩ ⟨hbyteUpper, hprefix⟩
      have hbyteUpper' : currentByte.val ≤ 32 := by
        simpa only using hbyteUpper
      have hprefix' : ∀ byte, byte < currentByte.val →
          radixInputByte current slot.val byte =
            generatedDigestByte child byte := by
        simpa only using hprefix
      unfold merkle.fixed_write_radix_child_loop.body
      by_cases hactive : currentByte.val < 32
      · have hactiveScalar : currentByte < 32#usize := by scalar_tac
        rw [if_pos hactiveScalar]
        obtain ⟨childByte, hchildRun, hchildValue⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Array.index_usize_spec child currentByte (by
              simpa [Array.length_eq] using hactive))
        rw [hchildRun]
        simp only [Aeneas.Std.bind_tc_ok, lift]
        let target := Std.Usize.wrapping_add
          (Std.Usize.wrapping_add 1#usize
            (Std.Usize.wrapping_mul slot 32#usize)) currentByte
        have htarget : target.val = 1 + slot.val * 32 + currentByte.val :=
          fixed_write_index_val slot currentByte hslot hactive
        have htargetBound : target.val < 129 := by omega
        obtain ⟨updated, hupdatedRun, hupdatedValue⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Array.update_spec current target childByte (by
              simpa [Array.length_eq] using htargetBound))
        rw [hupdatedRun]
        simp only [Aeneas.Std.bind_tc_ok, lift, Aeneas.Std.WP.spec,
          Aeneas.Std.WP.theta]
        have hnext := fixed_write_next_byte_val currentByte hactive
        subst updated
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hnext]
          omega
        · intro byte hbyte
          rw [hnext] at hbyte
          by_cases hbefore : byte < currentByte.val
          · have htargetNe :
                target.val ≠ 1 + slot.val * 32 + byte := by
              rw [htarget]
              omega
            unfold radixInputByte
            simp only [Array.set_val_eq]
            rw [List.set_getElem!_ne current.val target.val
              (1 + slot.val * 32 + byte) childByte (Or.inl htargetNe)]
            exact hprefix' byte hbefore
          · have hbyteEq : byte = currentByte.val := by omega
            subst byte
            unfold radixInputByte generatedDigestByte
            simp only [Array.set_val_eq]
            have htargetEq :
                target.val = 1 + slot.val * 32 + currentByte.val := htarget
            rw [List.set_getElem!_eq _ _ _ _ (by
              constructor
              · rw [← htarget]
                simpa [current.property] using htargetBound
              · exact htargetEq)]
            have hchildBound : currentByte.val < child.val.length := by
              simpa [child.property] using hactive
            change childByte = child.val[currentByte.val]!
            rw [hchildValue]
            exact (List.Inhabited_getElem_eq_getElem!
              child.val currentByte.val hchildBound)
        · rw [hnext]
          omega
      · have hdoneScalar : ¬ currentByte < 32#usize := by scalar_tac
        rw [if_neg hdoneScalar]
        intro byte hbyte
        apply hprefix' byte
        omega
    · simp [FixedWriteInvariant]
  have hloop :
      merkle.fixed_write_radix_child_loop input slot child 0#usize =
        .ok output := by
    simpa [merkle.fixed_write_radix_child] using hrun
  rw [hloop] at hspec
  simpa [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta,
    Aeneas.Std.WP.wp_return, FixedWritePost] using hspec

private def FixedWriteFrameInvariant (original : GeneratedRadixInput)
    (slot : Std.Usize) (state : GeneratedRadixInput × Std.Usize) : Prop :=
  state.2.val ≤ 32 ∧
    ∀ index, index < 129 →
      (index < 1 + slot.val * 32 ∨
        1 + slot.val * 32 + state.2.val ≤ index) →
      state.1.val[index]! = original.val[index]!

private def FixedWriteFramePost (original : GeneratedRadixInput)
    (slot : Std.Usize) (output : GeneratedRadixInput) : Prop :=
  ∀ index, index < 129 →
    (index < 1 + slot.val * 32 ∨
      1 + slot.val * 32 + 32 ≤ index) →
    output.val[index]! = original.val[index]!

/-- The fixed write changes no byte outside its selected 32-byte slot. -/
theorem fixed_write_radix_child_frame
    (input output : GeneratedRadixInput) (slot : Std.Usize)
    (child : GeneratedDigest) (hslot : slot.val < 4)
    (hrun : merkle.fixed_write_radix_child input slot child = .ok output) :
    ∀ index, index < 129 →
      (index < 1 + slot.val * 32 ∨
        1 + slot.val * 32 + 32 ≤ index) →
      output.val[index]! = input.val[index]! := by
  have hspec :
      merkle.fixed_write_radix_child_loop input slot child 0#usize
        ⦃ out => FixedWriteFramePost input slot out ⦄ := by
    simp only [merkle.fixed_write_radix_child_loop]
    apply Aeneas.Std.loop.spec_decr_nat
      (fun state : GeneratedRadixInput × Std.Usize => 32 - state.2.val)
      (FixedWriteFrameInvariant input slot)
      (FixedWriteFramePost input slot)
    · rintro ⟨current, currentByte⟩ ⟨hbyteUpper, hframe⟩
      have hbyteUpper' : currentByte.val ≤ 32 := by
        simpa only using hbyteUpper
      have hframe' : ∀ index, index < 129 →
          (index < 1 + slot.val * 32 ∨
            1 + slot.val * 32 + currentByte.val ≤ index) →
          current.val[index]! = input.val[index]! := by
        simpa only using hframe
      unfold merkle.fixed_write_radix_child_loop.body
      by_cases hactive : currentByte.val < 32
      · have hactiveScalar : currentByte < 32#usize := by scalar_tac
        rw [if_pos hactiveScalar]
        obtain ⟨childByte, hchildRun, _hchildValue⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Array.index_usize_spec child currentByte (by
              simpa [Array.length_eq] using hactive))
        rw [hchildRun]
        simp only [Aeneas.Std.bind_tc_ok, lift]
        let target := Std.Usize.wrapping_add
          (Std.Usize.wrapping_add 1#usize
            (Std.Usize.wrapping_mul slot 32#usize)) currentByte
        have htarget : target.val = 1 + slot.val * 32 + currentByte.val :=
          fixed_write_index_val slot currentByte hslot hactive
        have htargetBound : target.val < 129 := by omega
        obtain ⟨updated, hupdatedRun, hupdatedValue⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Array.update_spec current target childByte (by
              simpa [Array.length_eq] using htargetBound))
        rw [hupdatedRun]
        simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.WP.spec,
          Aeneas.Std.WP.theta]
        have hnext := fixed_write_next_byte_val currentByte hactive
        subst updated
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hnext]
          omega
        · intro index hindex houtside
          rw [hnext] at houtside
          have htargetNe : target.val ≠ index := by
            rw [htarget]
            rcases houtside with hleft | hright <;> omega
          simp only [Array.set_val_eq]
          rw [List.set_getElem!_ne current.val target.val index childByte
            (Or.inl htargetNe)]
          apply hframe' index hindex
          rcases houtside with hleft | hright
          · exact Or.inl hleft
          · exact Or.inr (by omega)
        · rw [hnext]
          omega
      · have hdoneScalar : ¬ currentByte < 32#usize := by scalar_tac
        rw [if_neg hdoneScalar]
        intro index hindex houtside
        apply hframe' index hindex
        rcases houtside with hleft | hright
        · exact Or.inl hleft
        · exact Or.inr (by omega)
    · simp [FixedWriteFrameInvariant]
  have hloop :
      merkle.fixed_write_radix_child_loop input slot child 0#usize =
        .ok output := by
    simpa [merkle.fixed_write_radix_child] using hrun
  rw [hloop] at hspec
  simpa [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta,
    Aeneas.Std.WP.wp_return, FixedWriteFramePost] using hspec

/-- The generated frontier-copy loop returns exactly the next 32 bytes. -/
theorem fixed_fill_radix_children_loop_exact
    (nodeBytes : Slice Std.U8) (nodePos : Std.Usize)
    (input output : GeneratedDigest)
    (hspace : nodePos.val + 32 ≤ nodeBytes.val.length)
    (hrun : merkle.fixed_fill_radix_children_loop nodeBytes nodePos input
      0#usize = .ok output) :
    ∀ byte, byte < 32 →
      generatedDigestByte output byte =
        nodeBytes.val[nodePos.val + byte]! := by
  have hspec :
      merkle.fixed_fill_radix_children_loop nodeBytes nodePos input 0#usize
        ⦃ out => FixedReadPost nodeBytes nodePos out ⦄ := by
    simp only [merkle.fixed_fill_radix_children_loop]
    apply Aeneas.Std.loop.spec_decr_nat
      (fun state : GeneratedDigest × Std.Usize => 32 - state.2.val)
      (FixedReadInvariant nodeBytes nodePos)
      (FixedReadPost nodeBytes nodePos)
    · rintro ⟨current, currentByte⟩ ⟨hbyteUpper, hprefix⟩
      have hbyteUpper' : currentByte.val ≤ 32 := by
        simpa only using hbyteUpper
      have hprefix' : ∀ byte, byte < currentByte.val →
          generatedDigestByte current byte =
            nodeBytes.val[nodePos.val + byte]! := by
        simpa only using hprefix
      unfold merkle.fixed_fill_radix_children_loop.body
      simp only [Prod.snd, Prod.fst]
      by_cases hactive : currentByte.val < 32
      · have hactiveScalar : currentByte < 32#usize := by scalar_tac
        rw [if_pos hactiveScalar]
        let source := Std.Usize.wrapping_add nodePos currentByte
        have hsource : source.val = nodePos.val + currentByte.val :=
          fixed_read_index_val nodeBytes nodePos currentByte hspace hactive
        have hsourceBound : source.val < nodeBytes.val.length := by
          rw [hsource]
          omega
        obtain ⟨sourceByte, hsourceRun, hsourceValue⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Slice.index_usize_spec nodeBytes source hsourceBound)
        simp only [lift, Aeneas.Std.bind_tc_ok]
        have hsourceRun' :
            Slice.index_usize nodeBytes
              (Std.Usize.wrapping_add nodePos currentByte) =
                .ok sourceByte := by
          simpa [source] using hsourceRun
        rw [hsourceRun']
        simp only [Aeneas.Std.bind_tc_ok, lift]
        obtain ⟨updated, hupdatedRun, hupdatedValue⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Array.update_spec current currentByte sourceByte (by
              simpa [Array.length_eq] using hactive))
        rw [hupdatedRun]
        simp only [Aeneas.Std.bind_tc_ok, lift, Aeneas.Std.WP.spec,
          Aeneas.Std.WP.theta]
        have hnext := fixed_write_next_byte_val currentByte hactive
        subst updated
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hnext]
          omega
        · intro byte hbyte
          rw [hnext] at hbyte
          by_cases hbefore : byte < currentByte.val
          · unfold generatedDigestByte
            simp only [Array.set_val_eq]
            rw [List.set_getElem!_ne current.val currentByte.val byte
              sourceByte (Or.inl (by omega))]
            exact hprefix' byte hbefore
          · have hbyteEq : byte = currentByte.val := by omega
            subst byte
            unfold generatedDigestByte
            simp only [Array.set_val_eq]
            rw [List.set_getElem!_eq current.val currentByte.val
              currentByte.val sourceByte (by
                exact ⟨by simpa [current.property] using hactive, rfl⟩)]
            rw [hsourceValue]
            change nodeBytes.val[source.val] =
              nodeBytes.val[nodePos.val + currentByte.val]!
            rw [← hsource]
            exact (List.Inhabited_getElem_eq_getElem!
              nodeBytes.val source.val hsourceBound)
        · rw [hnext]
          omega
      · have hdoneScalar : ¬ currentByte < 32#usize := by scalar_tac
        rw [if_neg hdoneScalar]
        intro byte hbyte
        exact hprefix' byte (by omega)
    · simp [FixedReadInvariant]
  rw [hrun] at hspec
  simpa [Aeneas.Std.WP.spec, Aeneas.Std.WP.theta,
    Aeneas.Std.WP.wp_return, FixedReadPost] using hspec

private theorem fixed_add_32_val
    (nodePos : Std.Usize)
    (hroom : nodePos.val + 32 < UScalar.size .Usize) :
    (Std.Usize.wrapping_add nodePos 32#usize).val = nodePos.val + 32 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  apply Nat.mod_eq_of_lt
  simpa only [UScalar.size_UScalarTyUsize] using hroom

private theorem fixed_slot_succ_val
    (slot : Std.Usize) (hslot : slot.val < 4) :
    (Std.Usize.wrapping_add slot 1#usize).val = slot.val + 1 :=
  fixed_write_next_byte_val slot (by omega)

private theorem fixed_usize_succ_val_of_room
    (value : Std.Usize)
    (hroom : value.val + 1 < UScalar.size .Usize) :
    (Std.Usize.wrapping_add value 1#usize).val = value.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  apply Nat.mod_eq_of_lt
  simpa only [UScalar.size_UScalarTyUsize] using hroom

/-- One exact nonterminal source step of the generated four-child scan.  The
disjunction says whether the child came from the live level or the next
32-byte frontier chunk; both cursor updates and the recursive call are kept. -/
structure GeneratedFillStep
    (nodeBytes : Slice Std.U8) (level : Slice GeneratedDigest)
    (present : Std.U8) (slot nodePos valuePos : Std.Usize)
    (input : GeneratedRadixInput)
    (finalInput : GeneratedRadixInput)
    (finalNodePos finalValuePos : Std.Usize) where
  child : GeneratedDigest
  input' : GeneratedRadixInput
  nextNodePos : Std.Usize
  nextValuePos : Std.Usize
  source :
    ((present &&& Std.U8.wrapping_shl 1#u8 (usizeShiftCount slot) != 0#u8) ∧
      valuePos.val < level.val.length ∧
      child = level.val[valuePos.val]! ∧
      nextNodePos = nodePos ∧
      nextValuePos.val = valuePos.val + 1) ∨
    ((¬ (present &&& Std.U8.wrapping_shl 1#u8 (usizeShiftCount slot) !=
        0#u8)) ∧
      nodePos.val + 32 ≤ nodeBytes.val.length ∧
      (∀ byte, byte < 32 → generatedDigestByte child byte =
        nodeBytes.val[nodePos.val + byte]!) ∧
      nextNodePos.val = nodePos.val + 32 ∧
      nextValuePos = valuePos)
  write_run : merkle.fixed_write_radix_child input slot child = .ok input'
  recurse_run :
    merkle.fixed_fill_radix_children nodeBytes level present
      (Std.Usize.wrapping_add slot 1#usize) nextNodePos nextValuePos input' =
        .ok (some (finalInput, finalNodePos, finalValuePos))

/-- Inverting a successful nonterminal generated child scan exposes its exact
source, exact write, cursor update, and recursive tail.  `hroom` is the
ordinary released-proof size bound that excludes `usize` wraparound. -/
theorem fixed_fill_radix_children_success_step
    (nodeBytes : Slice Std.U8) (level : Slice GeneratedDigest)
    (present : Std.U8) (slot nodePos valuePos : Std.Usize)
    (input finalInput : GeneratedRadixInput)
    (finalNodePos finalValuePos : Std.Usize)
    (hslot : slot.val < 4)
    (hnodePos : nodePos.val ≤ nodeBytes.val.length)
    (hroom : nodeBytes.val.length + 32 < UScalar.size .Usize)
    (hrun : merkle.fixed_fill_radix_children nodeBytes level present slot
      nodePos valuePos input =
        .ok (some (finalInput, finalNodePos, finalValuePos))) :
    Nonempty (GeneratedFillStep nodeBytes level present slot nodePos valuePos
      input finalInput finalNodePos finalValuePos) := by
  rw [merkle.fixed_fill_radix_children.eq_def] at hrun
  have hnotDone : ¬ slot ≥ 4#usize := by scalar_tac
  rw [if_neg hnotDone] at hrun
  simp only [lift, Aeneas.Std.bind_tc_ok] at hrun
  let presentBit :=
    present &&& Std.U8.wrapping_shl 1#u8 (usizeShiftCount slot) != 0#u8
  by_cases hpresent : presentBit
  · have hpresent' :
        present &&& Std.U8.wrapping_shl 1#u8 (usizeShiftCount slot) !=
          0#u8 := by
      simpa [presentBit] using hpresent
    rw [if_pos hpresent'] at hrun
    have hvalueBound : valuePos.val < level.val.length := by
      by_contra hpast
      have hpast' : valuePos ≥ Slice.len level := by scalar_tac
      rw [if_pos hpast'] at hrun
      simp at hrun
    have hnotPast : ¬ valuePos ≥ Slice.len level := by scalar_tac
    rw [if_neg hnotPast] at hrun
    have hvalueRun : Slice.index_usize level valuePos =
        .ok level.val[valuePos.val] := by
      unfold Slice.index_usize
      rw [Slice.getElem?_Usize_eq]
      simp [hvalueBound]
    rw [hvalueRun] at hrun
    simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
    generalize hwrite : merkle.fixed_write_radix_child input slot
      level.val[valuePos.val] = writeResult at hrun
    cases writeResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok input' =>
      simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
      refine ⟨{
        child := level.val[valuePos.val]
        input' := input'
        nextNodePos := nodePos
        nextValuePos := Std.Usize.wrapping_add valuePos 1#usize
        source := Or.inl ⟨hpresent', hvalueBound, ?_, rfl, ?_⟩
        write_run := hwrite
        recurse_run := hrun }⟩
      · exact (List.Inhabited_getElem_eq_getElem!
          level.val valuePos.val hvalueBound)
      · apply fixed_usize_succ_val_of_room
        have hsizes : UScalar.size .Usize = Usize.size :=
          UScalar.size_UScalarTyUsize
        have hmax : Usize.max < Usize.size := by
          rcases System.Platform.numBits_eq with hbits | hbits <;>
            simp [Usize.max, Usize.size, Usize.numBits, hbits]
        rw [hsizes]
        have hlength := level.property
        omega
  · have habsent :
        ¬ (present &&& Std.U8.wrapping_shl 1#u8 (usizeShiftCount slot) !=
          0#u8) := by
      simpa [presentBit] using hpresent
    rw [if_neg habsent] at hrun
    have haddRoom : nodePos.val + 32 < UScalar.size .Usize := by omega
    have hadd := fixed_add_32_val nodePos haddRoom
    have hspace : nodePos.val + 32 ≤ nodeBytes.val.length := by
      by_contra hpast
      have hpast' :
          Std.Usize.wrapping_add nodePos 32#usize > Slice.len nodeBytes := by
        change (Std.Usize.wrapping_add nodePos 32#usize).val >
          nodeBytes.val.length
        rw [hadd]
        omega
      rw [if_pos hpast'] at hrun
      simp at hrun
    have hnotPast :
        ¬ Std.Usize.wrapping_add nodePos 32#usize > Slice.len nodeBytes := by
      change ¬ (Std.Usize.wrapping_add nodePos 32#usize).val >
        nodeBytes.val.length
      rw [hadd]
      omega
    rw [if_neg hnotPast] at hrun
    generalize hread :
      merkle.fixed_fill_radix_children_loop nodeBytes nodePos
        (Array.repeat 32#usize 0#u8) 0#usize = readResult at hrun
    cases readResult with
    | fail error => simp at hrun
    | div => simp at hrun
    | ok child =>
      simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
      generalize hwrite : merkle.fixed_write_radix_child input slot child =
        writeResult at hrun
      cases writeResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok input' =>
        simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
        refine ⟨{
          child := child
          input' := input'
          nextNodePos := Std.Usize.wrapping_add nodePos 32#usize
          nextValuePos := valuePos
          source := Or.inr ⟨habsent, hspace, ?_, hadd, rfl⟩
          write_run := hwrite
          recurse_run := hrun }⟩
        exact fixed_fill_radix_children_loop_exact nodeBytes nodePos
          (Array.repeat 32#usize 0#u8) child hspace hread

theorem GeneratedFillStep.nextNodePos_le
    {nodeBytes : Slice Std.U8} {level : Slice GeneratedDigest}
    {present : Std.U8} {slot nodePos valuePos : Std.Usize}
    {input finalInput : GeneratedRadixInput}
    {finalNodePos finalValuePos : Std.Usize}
    (step : GeneratedFillStep nodeBytes level present slot nodePos valuePos
      input finalInput finalNodePos finalValuePos)
    (hnodePos : nodePos.val ≤ nodeBytes.val.length) :
    step.nextNodePos.val ≤ nodeBytes.val.length := by
  rcases step.source with hpresent | hfrontier
  · rw [hpresent.2.2.2.1]
    exact hnodePos
  · omega

/-- Exact four-slot trace returned by a successful generated child scan from
slot zero.  All four source decisions, writes, and tail calls are retained;
the terminal equalities show that no fifth slot is read or written. -/
structure GeneratedFourChildTrace
    (nodeBytes : Slice Std.U8) (level : Slice GeneratedDigest)
    (present : Std.U8) (nodePos valuePos : Std.Usize)
    (input finalInput : GeneratedRadixInput)
    (finalNodePos finalValuePos : Std.Usize) where
  step0 : GeneratedFillStep nodeBytes level present 0#usize nodePos valuePos
    input finalInput finalNodePos finalValuePos
  step1 : GeneratedFillStep nodeBytes level present 1#usize
    step0.nextNodePos step0.nextValuePos step0.input'
    finalInput finalNodePos finalValuePos
  step2 : GeneratedFillStep nodeBytes level present 2#usize
    step1.nextNodePos step1.nextValuePos step1.input'
    finalInput finalNodePos finalValuePos
  step3 : GeneratedFillStep nodeBytes level present 3#usize
    step2.nextNodePos step2.nextValuePos step2.input'
    finalInput finalNodePos finalValuePos
  finalInput_eq : finalInput = step3.input'
  finalNodePos_eq : finalNodePos = step3.nextNodePos
  finalValuePos_eq : finalValuePos = step3.nextValuePos

private theorem fixed_slot_0_succ :
    Std.Usize.wrapping_add 0#usize 1#usize = 1#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (1#usize).hSize; scalar_tac)]
  norm_num

private theorem fixed_slot_1_succ :
    Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (2#usize).hSize; scalar_tac)]
  norm_num

private theorem fixed_slot_2_succ :
    Std.Usize.wrapping_add 2#usize 1#usize = 3#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (3#usize).hSize; scalar_tac)]
  norm_num

private theorem fixed_slot_3_succ :
    Std.Usize.wrapping_add 3#usize 1#usize = 4#usize := by
  apply UScalar.val_eq_imp
  rw [Std.Usize.wrapping_add_val_eq,
    Nat.mod_eq_of_lt (by have h := (4#usize).hSize; scalar_tac)]
  norm_num

/-- A successful generated fill from slot zero is exactly four child steps,
with no omitted, duplicated, or reordered slot. -/
theorem fixed_fill_radix_children_success_yields_four_steps
    (nodeBytes : Slice Std.U8) (level : Slice GeneratedDigest)
    (present : Std.U8) (nodePos valuePos : Std.Usize)
    (input finalInput : GeneratedRadixInput)
    (finalNodePos finalValuePos : Std.Usize)
    (hnodePos : nodePos.val ≤ nodeBytes.val.length)
    (hroom : nodeBytes.val.length + 32 < UScalar.size .Usize)
    (hrun : merkle.fixed_fill_radix_children nodeBytes level present 0#usize
      nodePos valuePos input =
        .ok (some (finalInput, finalNodePos, finalValuePos))) :
    Nonempty (GeneratedFourChildTrace nodeBytes level present nodePos valuePos
      input finalInput finalNodePos finalValuePos) := by
  let step0 := Classical.choice
    (fixed_fill_radix_children_success_step nodeBytes level present 0#usize
      nodePos valuePos input finalInput finalNodePos finalValuePos
      (by norm_num) hnodePos hroom hrun)
  have hnode1 := step0.nextNodePos_le hnodePos
  have hrun1 :
      merkle.fixed_fill_radix_children nodeBytes level present 1#usize
        step0.nextNodePos step0.nextValuePos step0.input' =
          .ok (some (finalInput, finalNodePos, finalValuePos)) := by
    simpa only [fixed_slot_0_succ] using step0.recurse_run
  let step1 := Classical.choice
    (fixed_fill_radix_children_success_step nodeBytes level present 1#usize
      step0.nextNodePos step0.nextValuePos step0.input' finalInput
      finalNodePos finalValuePos (by norm_num) hnode1 hroom hrun1)
  have hnode2 := step1.nextNodePos_le hnode1
  have hrun2 :
      merkle.fixed_fill_radix_children nodeBytes level present 2#usize
        step1.nextNodePos step1.nextValuePos step1.input' =
          .ok (some (finalInput, finalNodePos, finalValuePos)) := by
    simpa only [fixed_slot_1_succ] using step1.recurse_run
  let step2 := Classical.choice
    (fixed_fill_radix_children_success_step nodeBytes level present 2#usize
      step1.nextNodePos step1.nextValuePos step1.input' finalInput
      finalNodePos finalValuePos (by norm_num) hnode2 hroom hrun2)
  have hnode3 := step2.nextNodePos_le hnode2
  have hrun3 :
      merkle.fixed_fill_radix_children nodeBytes level present 3#usize
        step2.nextNodePos step2.nextValuePos step2.input' =
          .ok (some (finalInput, finalNodePos, finalValuePos)) := by
    simpa only [fixed_slot_2_succ] using step2.recurse_run
  let step3 := Classical.choice
    (fixed_fill_radix_children_success_step nodeBytes level present 3#usize
      step2.nextNodePos step2.nextValuePos step2.input' finalInput
      finalNodePos finalValuePos (by norm_num) hnode3 hroom hrun3)
  have hterminal :
      merkle.fixed_fill_radix_children nodeBytes level present 4#usize
        step3.nextNodePos step3.nextValuePos step3.input' =
          .ok (some (finalInput, finalNodePos, finalValuePos)) := by
    simpa only [fixed_slot_3_succ] using step3.recurse_run
  have hdone :=
    AspisV5MerkleGeneratedHelperBridge.fixed_fill_radix_children_done
      nodeBytes level present 4#usize step3.nextNodePos
      step3.nextValuePos step3.input' (by norm_num)
  rw [hdone] at hterminal
  injection hterminal with hsome
  have htriple := Option.some.inj hsome
  have hinput : step3.input' = finalInput := congrArg Prod.fst htriple
  have hnode : step3.nextNodePos = finalNodePos :=
    congrArg (fun value => value.2.1) htriple
  have hvalue : step3.nextValuePos = finalValuePos :=
    congrArg (fun value => value.2.2) htriple
  exact ⟨{
    step0 := step0
    step1 := step1
    step2 := step2
    step3 := step3
    finalInput_eq := hinput.symm
    finalNodePos_eq := hnode.symm
    finalValuePos_eq := hvalue.symm }⟩

theorem GeneratedFourChildTrace.finalNodePos_le
    {nodeBytes : Slice Std.U8} {level : Slice GeneratedDigest}
    {present : Std.U8} {nodePos valuePos : Std.Usize}
    {input finalInput : GeneratedRadixInput}
    {finalNodePos finalValuePos : Std.Usize}
    (trace : GeneratedFourChildTrace nodeBytes level present nodePos valuePos
      input finalInput finalNodePos finalValuePos)
    (hnodePos : nodePos.val ≤ nodeBytes.val.length) :
    finalNodePos.val ≤ nodeBytes.val.length := by
  have h0 := trace.step0.nextNodePos_le hnodePos
  have h1 := trace.step1.nextNodePos_le h0
  have h2 := trace.step2.nextNodePos_le h1
  have h3 := trace.step3.nextNodePos_le h2
  rw [trace.finalNodePos_eq]
  exact h3

theorem fixed_write_preserves_other_slot
    (input output : GeneratedRadixInput)
    (writtenSlot targetSlot : Std.Usize) (child : GeneratedDigest)
    (hwritten : writtenSlot.val < 4) (htarget : targetSlot.val < 4)
    (hne : writtenSlot.val ≠ targetSlot.val)
    (hrun : merkle.fixed_write_radix_child input writtenSlot child =
      .ok output) :
    ∀ byte, byte < 32 →
      radixInputByte output targetSlot.val byte =
        radixInputByte input targetSlot.val byte := by
  intro byte hbyte
  have hframe := fixed_write_radix_child_frame input output writtenSlot child
    hwritten hrun (1 + targetSlot.val * 32 + byte) (by omega) (by
      by_cases horder : targetSlot.val < writtenSlot.val
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))
  exact hframe

def GeneratedFourChildTrace.child
    {nodeBytes : Slice Std.U8} {level : Slice GeneratedDigest}
    {present : Std.U8} {nodePos valuePos : Std.Usize}
    {input finalInput : GeneratedRadixInput}
    {finalNodePos finalValuePos : Std.Usize}
    (trace : GeneratedFourChildTrace nodeBytes level present nodePos valuePos
      input finalInput finalNodePos finalValuePos) :
    Fin 4 → GeneratedDigest
  | ⟨0, _⟩ => trace.step0.child
  | ⟨1, _⟩ => trace.step1.child
  | ⟨2, _⟩ => trace.step2.child
  | ⟨3, _⟩ => trace.step3.child

/-- The terminal 129-byte group input contains exactly the four children
selected by the source trace, in literal slot order. -/
theorem GeneratedFourChildTrace.final_slots_exact
    {nodeBytes : Slice Std.U8} {level : Slice GeneratedDigest}
    {present : Std.U8} {nodePos valuePos : Std.Usize}
    {input finalInput : GeneratedRadixInput}
    {finalNodePos finalValuePos : Std.Usize}
    (trace : GeneratedFourChildTrace nodeBytes level present nodePos valuePos
      input finalInput finalNodePos finalValuePos) :
    ∀ slot : Fin 4, ∀ byte, byte < 32 →
      radixInputByte finalInput slot.val byte =
        generatedDigestByte (trace.child slot) byte := by
  intro slot byte hbyte
  have hwrite0 := fixed_write_radix_child_exact input trace.step0.input'
    0#usize trace.step0.child (by norm_num) trace.step0.write_run byte hbyte
  have hwrite1 := fixed_write_radix_child_exact trace.step0.input'
    trace.step1.input' 1#usize trace.step1.child (by norm_num)
    trace.step1.write_run byte hbyte
  have hwrite2 := fixed_write_radix_child_exact trace.step1.input'
    trace.step2.input' 2#usize trace.step2.child (by norm_num)
    trace.step2.write_run byte hbyte
  have hwrite3 := fixed_write_radix_child_exact trace.step2.input'
    trace.step3.input' 3#usize trace.step3.child (by norm_num)
    trace.step3.write_run byte hbyte
  have h10 := fixed_write_preserves_other_slot trace.step0.input'
    trace.step1.input' 1#usize 0#usize trace.step1.child
    (by norm_num) (by norm_num) (by norm_num) trace.step1.write_run byte hbyte
  have h20 := fixed_write_preserves_other_slot trace.step1.input'
    trace.step2.input' 2#usize 0#usize trace.step2.child
    (by norm_num) (by norm_num) (by norm_num) trace.step2.write_run byte hbyte
  have h21 := fixed_write_preserves_other_slot trace.step1.input'
    trace.step2.input' 2#usize 1#usize trace.step2.child
    (by norm_num) (by norm_num) (by norm_num) trace.step2.write_run byte hbyte
  have h30 := fixed_write_preserves_other_slot trace.step2.input'
    trace.step3.input' 3#usize 0#usize trace.step3.child
    (by norm_num) (by norm_num) (by norm_num) trace.step3.write_run byte hbyte
  have h31 := fixed_write_preserves_other_slot trace.step2.input'
    trace.step3.input' 3#usize 1#usize trace.step3.child
    (by norm_num) (by norm_num) (by norm_num) trace.step3.write_run byte hbyte
  have h32 := fixed_write_preserves_other_slot trace.step2.input'
    trace.step3.input' 3#usize 2#usize trace.step3.child
    (by norm_num) (by norm_num) (by norm_num) trace.step3.write_run byte hbyte
  have hfinal : radixInputByte finalInput slot.val byte =
      radixInputByte trace.step3.input' slot.val byte :=
    congrArg (fun value => radixInputByte value slot.val byte)
      trace.finalInput_eq
  fin_cases slot
  · exact hfinal.trans (h30.trans (h20.trans (h10.trans hwrite0)))
  · exact hfinal.trans (h31.trans (h21.trans hwrite1))
  · exact hfinal.trans (h32.trans hwrite2)
  · exact hfinal.trans hwrite3

theorem GeneratedFourChildTrace.final_tag_eq_initial
    {nodeBytes : Slice Std.U8} {level : Slice GeneratedDigest}
    {present : Std.U8} {nodePos valuePos : Std.Usize}
    {input finalInput : GeneratedRadixInput}
    {finalNodePos finalValuePos : Std.Usize}
    (trace : GeneratedFourChildTrace nodeBytes level present nodePos valuePos
      input finalInput finalNodePos finalValuePos) :
    finalInput.val[0]! = input.val[0]! := by
  have h0 := fixed_write_radix_child_frame input trace.step0.input'
    0#usize trace.step0.child (by norm_num) trace.step0.write_run 0
    (by norm_num) (Or.inl (by norm_num))
  have h1 := fixed_write_radix_child_frame trace.step0.input'
    trace.step1.input' 1#usize trace.step1.child (by norm_num)
    trace.step1.write_run 0 (by norm_num) (Or.inl (by norm_num))
  have h2 := fixed_write_radix_child_frame trace.step1.input'
    trace.step2.input' 2#usize trace.step2.child (by norm_num)
    trace.step2.write_run 0 (by norm_num) (Or.inl (by norm_num))
  have h3 := fixed_write_radix_child_frame trace.step2.input'
    trace.step3.input' 3#usize trace.step3.child (by norm_num)
    trace.step3.write_run 0 (by norm_num) (Or.inl (by norm_num))
  have hfinal : finalInput.val[0]! = trace.step3.input'.val[0]! :=
    congrArg (fun value => value.val[0]!) trace.finalInput_eq
  exact hfinal.trans (h3.trans (h2.trans (h1.trans h0)))

/-- The complete generated hash preimage is the preserved domain byte followed
by the four exact child digests. -/
theorem GeneratedFourChildTrace.final_input_eq_children
    {nodeBytes : Slice Std.U8} {level : Slice GeneratedDigest}
    {present : Std.U8} {nodePos valuePos : Std.Usize}
    {input finalInput : GeneratedRadixInput}
    {finalNodePos finalValuePos : Std.Usize}
    (trace : GeneratedFourChildTrace nodeBytes level present nodePos valuePos
      input finalInput finalNodePos finalValuePos) :
    finalInput.val = [input.val[0]!] ++
      ((trace.child 0).val ++ ((trace.child 1).val ++
        ((trace.child 2).val ++ (trace.child 3).val))) := by
  apply List.ext_getElem
  · simp [finalInput.property, (trace.child 0).property,
      (trace.child 1).property, (trace.child 2).property,
      (trace.child 3).property]
  · intro index hleft hright
    rw [List.Inhabited_getElem_eq_getElem! finalInput.val index hleft,
      List.Inhabited_getElem_eq_getElem! _ index hright]
    by_cases hzero : index = 0
    · subst index
      simpa using trace.final_tag_eq_initial
    by_cases hslot0 : index < 33
    · have hbyte : index - 1 < 32 := by omega
      have hslot := trace.final_slots_exact (0 : Fin 4) (index - 1) hbyte
      have hrhs :
          ([input.val[0]!] ++ ((trace.child 0).val ++
            ((trace.child 1).val ++ ((trace.child 2).val ++
              (trace.child 3).val))))[index]! =
              (trace.child 0).val[index - 1]! := by
        rw [List.getElem!_append_right
          [input.val[0]!]
          ((trace.child 0).val ++ ((trace.child 1).val ++
            ((trace.child 2).val ++ (trace.child 3).val)))
          index (by simp; omega)]
        change ((trace.child 0).val ++ ((trace.child 1).val ++
          ((trace.child 2).val ++ (trace.child 3).val)))[index - 1]! = _
        rw [List.getElem!_append_left
          (trace.child 0).val
          ((trace.child 1).val ++ ((trace.child 2).val ++
            (trace.child 3).val))
          (index - 1) (by simpa [(trace.child 0).property] using hbyte)]
      rw [hrhs]
      change finalInput.val[index]! = (trace.child 0).val[index - 1]!
      change finalInput.val[1 + 0 * 32 + (index - 1)]! =
        (trace.child 0).val[index - 1]! at hslot
      rw [show 1 + 0 * 32 + (index - 1) = index by omega] at hslot
      exact hslot
    by_cases hslot1 : index < 65
    · have hbyte : index - 33 < 32 := by omega
      have hslot := trace.final_slots_exact (1 : Fin 4) (index - 33) hbyte
      have hrhs :
          ([input.val[0]!] ++ ((trace.child 0).val ++
            ((trace.child 1).val ++ ((trace.child 2).val ++
              (trace.child 3).val))))[index]! =
              (trace.child 1).val[index - 33]! := by
        rw [List.getElem!_append_right
          [input.val[0]!]
          ((trace.child 0).val ++ ((trace.child 1).val ++
            ((trace.child 2).val ++ (trace.child 3).val)))
          index (by simp; omega)]
        change ((trace.child 0).val ++ ((trace.child 1).val ++
          ((trace.child 2).val ++ (trace.child 3).val)))[index - 1]! = _
        rw [List.getElem!_append_right
          (trace.child 0).val
          ((trace.child 1).val ++ ((trace.child 2).val ++
            (trace.child 3).val))
          (index - 1) (by simp [(trace.child 0).property]; omega)]
        have hoff0 : index - 1 - (trace.child 0).val.length =
            index - 33 := by
          have hlen : (trace.child 0).val.length = 32 := by
            simpa using (trace.child 0).property
          rw [hlen]
          omega
        rw [hoff0]
        rw [List.getElem!_append_left
          (trace.child 1).val
          ((trace.child 2).val ++ (trace.child 3).val)
          (index - 33) (by simpa [(trace.child 1).property] using hbyte)]
      rw [hrhs]
      change finalInput.val[index]! = (trace.child 1).val[index - 33]!
      change finalInput.val[1 + 1 * 32 + (index - 33)]! =
        (trace.child 1).val[index - 33]! at hslot
      rw [show 1 + 1 * 32 + (index - 33) = index by omega] at hslot
      exact hslot
    by_cases hslot2 : index < 97
    · have hbyte : index - 65 < 32 := by omega
      have hslot := trace.final_slots_exact (2 : Fin 4) (index - 65) hbyte
      have hrhs :
          ([input.val[0]!] ++ ((trace.child 0).val ++
            ((trace.child 1).val ++ ((trace.child 2).val ++
              (trace.child 3).val))))[index]! =
              (trace.child 2).val[index - 65]! := by
        rw [List.getElem!_append_right
          [input.val[0]!]
          ((trace.child 0).val ++ ((trace.child 1).val ++
            ((trace.child 2).val ++ (trace.child 3).val)))
          index (by simp; omega)]
        change ((trace.child 0).val ++ ((trace.child 1).val ++
          ((trace.child 2).val ++ (trace.child 3).val)))[index - 1]! = _
        rw [List.getElem!_append_right
          (trace.child 0).val
          ((trace.child 1).val ++ ((trace.child 2).val ++
            (trace.child 3).val))
          (index - 1) (by simp [(trace.child 0).property]; omega)]
        have hoff0 : index - 1 - (trace.child 0).val.length =
            index - 33 := by
          have hlen : (trace.child 0).val.length = 32 := by
            simpa using (trace.child 0).property
          rw [hlen]
          omega
        rw [hoff0]
        rw [List.getElem!_append_right
          (trace.child 1).val
          ((trace.child 2).val ++ (trace.child 3).val)
          (index - 33) (by simp [(trace.child 1).property]; omega)]
        have hoff1 : index - 33 - (trace.child 1).val.length =
            index - 65 := by
          have hlen : (trace.child 1).val.length = 32 := by
            simpa using (trace.child 1).property
          rw [hlen]
          omega
        rw [hoff1]
        rw [List.getElem!_append_left
          (trace.child 2).val (trace.child 3).val
          (index - 65) (by simpa [(trace.child 2).property] using hbyte)]
      rw [hrhs]
      change finalInput.val[index]! = (trace.child 2).val[index - 65]!
      change finalInput.val[1 + 2 * 32 + (index - 65)]! =
        (trace.child 2).val[index - 65]! at hslot
      rw [show 1 + 2 * 32 + (index - 65) = index by omega] at hslot
      exact hslot
    · have hindex : index < 129 := by
        simpa [finalInput.property] using hleft
      have hbyte : index - 97 < 32 := by omega
      have hslot := trace.final_slots_exact (3 : Fin 4) (index - 97) hbyte
      have hrhs :
          ([input.val[0]!] ++ ((trace.child 0).val ++
            ((trace.child 1).val ++ ((trace.child 2).val ++
              (trace.child 3).val))))[index]! =
              (trace.child 3).val[index - 97]! := by
        rw [List.getElem!_append_right
          [input.val[0]!]
          ((trace.child 0).val ++ ((trace.child 1).val ++
            ((trace.child 2).val ++ (trace.child 3).val)))
          index (by simp; omega)]
        change ((trace.child 0).val ++ ((trace.child 1).val ++
          ((trace.child 2).val ++ (trace.child 3).val)))[index - 1]! = _
        rw [List.getElem!_append_right
          (trace.child 0).val
          ((trace.child 1).val ++ ((trace.child 2).val ++
            (trace.child 3).val))
          (index - 1) (by simp [(trace.child 0).property]; omega)]
        have hoff0 : index - 1 - (trace.child 0).val.length =
            index - 33 := by
          have hlen : (trace.child 0).val.length = 32 := by
            simpa using (trace.child 0).property
          rw [hlen]
          omega
        rw [hoff0]
        rw [List.getElem!_append_right
          (trace.child 1).val
          ((trace.child 2).val ++ (trace.child 3).val)
          (index - 33) (by simp [(trace.child 1).property]; omega)]
        have hoff1 : index - 33 - (trace.child 1).val.length =
            index - 65 := by
          have hlen : (trace.child 1).val.length = 32 := by
            simpa using (trace.child 1).property
          rw [hlen]
          omega
        rw [hoff1]
        rw [List.getElem!_append_right
          (trace.child 2).val (trace.child 3).val
          (index - 65) (by simp [(trace.child 2).property]; omega)]
        have hoff2 : index - 65 - (trace.child 2).val.length =
            index - 97 := by
          have hlen : (trace.child 2).val.length = 32 := by
            simpa using (trace.child 2).property
          rw [hlen]
          omega
        rw [hoff2]
      rw [hrhs]
      change finalInput.val[index]! = (trace.child 3).val[index - 97]!
      change finalInput.val[1 + 3 * 32 + (index - 97)]! =
        (trace.child 3).val[index - 97]! at hslot
      rw [show 1 + 3 * 32 + (index - 97) = index by omega] at hslot
      exact hslot

/-- Under the sole executable hash boundary, the digest appended by a group
is exactly the maintained model's domain-separated radix-four parent. -/
theorem GeneratedFourChildTrace.hash_exact
    {nodeBytes : Slice Std.U8} {level : Slice GeneratedDigest}
    {present : Std.U8} {nodePos valuePos : Std.Usize}
    {input finalInput : GeneratedRadixInput}
    {finalNodePos finalValuePos : Std.Usize}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (trace : GeneratedFourChildTrace nodeBytes level present nodePos valuePos
      input finalInput finalNodePos finalValuePos)
    (hdomain : input.val[0]! = merkle.DOM_NODE4)
    (digest : GeneratedDigest)
    (hhashRun :
      merkle.fixed_hashv
          (Array.to_slice (Array.make 1#usize [Array.to_slice finalInput])) =
        .ok digest) :
    generatedArrayToDigest digest =
      (sha256MerkleHashing sha256).radix4Node
        (fun slot => generatedArrayToDigest (trace.child slot)) := by
  have hbytes : finalInput.val.map generatedU8ToByte =
      [0x12] ++
        digestBytes (generatedArrayToDigest (trace.child 0)) ++
        digestBytes (generatedArrayToDigest (trace.child 1)) ++
        digestBytes (generatedArrayToDigest (trace.child 2)) ++
        digestBytes (generatedArrayToDigest (trace.child 3)) := by
    rw [trace.final_input_eq_children, List.map_append, List.map_append,
      List.map_append, List.map_append,
      digestBytes_generatedArrayToDigest,
      digestBytes_generatedArrayToDigest,
      digestBytes_generatedArrayToDigest,
      digestBytes_generatedArrayToDigest]
    have htag : generatedU8ToByte input.val[0]! = 0x12 := by
      rw [hdomain]
      rw [merkle.DOM_NODE4.eq_def]
      rfl
    simp only [List.map_singleton, htag]
    simp [List.append_assoc]
  have hexact := hhash _ digest hhashRun
  simp [Array.make, Array.val_to_slice] at hexact
  rw [hbytes] at hexact
  simpa [sha256MerkleHashing, hashInputBytes] using hexact

/-! ## Exact recursive group execution -/

/-- One nonterminal iteration of the generated group helper.  This retains
the exact mask byte, initialized domain-separated input, four-child source
trace, hash call, vector append, cursor results, and recursive tail. -/
structure GeneratedGroupStep
    (nodeBytes : Slice Std.U8) (level : Slice GeneratedDigest)
    (masks : Slice Std.U8) (maskPos nodePos valuePos : Std.Usize)
    (next : GeneratedDigestVec)
    (finalNext : GeneratedDigestVec)
    (finalNodePos finalValuePos : Std.Usize) where
  present : Std.U8
  input : GeneratedRadixInput
  filledInput : GeneratedRadixInput
  nextNodePos : Std.Usize
  nextValuePos : Std.Usize
  digest : GeneratedDigest
  next' : GeneratedDigestVec
  init_run :
    Array.update (Array.repeat 129#usize 0#u8) 0#usize merkle.DOM_NODE4 =
      .ok input
  mask_run : Slice.index_usize masks maskPos = .ok present
  fill_run :
    merkle.fixed_fill_radix_children nodeBytes level present 0#usize nodePos
        valuePos input =
      .ok (some (filledInput, nextNodePos, nextValuePos))
  children : GeneratedFourChildTrace nodeBytes level present nodePos valuePos
    input filledInput nextNodePos nextValuePos
  hash_run :
    merkle.fixed_hashv
        (Array.to_slice (Array.make 1#usize [Array.to_slice filledInput])) =
      .ok digest
  push_run : alloc.vec.Vec.push next digest = .ok next'
  recurse_run :
    merkle.fixed_hash_radix_groups nodeBytes level masks
        (Std.Usize.wrapping_add maskPos 1#usize) nextNodePos nextValuePos next' =
      .ok (some (finalNext, finalNodePos, finalValuePos))

/-- Invert one successful nonterminal group iteration into the exact generated
operations.  The ordinary `usize` room and frontier-cursor premises are kept
explicit and are discharged from the released proof-size bounds upstream. -/
theorem fixed_hash_radix_groups_success_step
    (nodeBytes : Slice Std.U8) (level : Slice GeneratedDigest)
    (masks : Slice Std.U8) (maskPos nodePos valuePos : Std.Usize)
    (next finalNext : GeneratedDigestVec)
    (finalNodePos finalValuePos : Std.Usize)
    (hmaskPos : maskPos.val < masks.val.length)
    (hnodePos : nodePos.val ≤ nodeBytes.val.length)
    (hroom : nodeBytes.val.length + 32 < UScalar.size .Usize)
    (hrun :
      merkle.fixed_hash_radix_groups nodeBytes level masks maskPos nodePos
          valuePos next =
        .ok (some (finalNext, finalNodePos, finalValuePos))) :
    Nonempty (GeneratedGroupStep nodeBytes level masks maskPos nodePos valuePos
      next finalNext finalNodePos finalValuePos) := by
  rw [merkle.fixed_hash_radix_groups.eq_def] at hrun
  have hnotDone : ¬ maskPos ≥ Slice.len masks := by
    change ¬ maskPos.val ≥ masks.val.length
    omega
  rw [if_neg hnotDone] at hrun
  dsimp only at hrun
  generalize hinit :
    Array.update (Array.repeat 129#usize 0#u8) 0#usize merkle.DOM_NODE4 =
      initResult
  rw [hinit] at hrun
  cases initResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok input =>
    simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
    generalize hmask : Slice.index_usize masks maskPos = maskResult
    rw [hmask] at hrun
    cases maskResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | ok present =>
      simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
      generalize hfill :
        merkle.fixed_fill_radix_children nodeBytes level present 0#usize
          nodePos valuePos input = fillResult
      rw [hfill] at hrun
      cases fillResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok fillOption =>
        cases fillOption with
        | none => simp [Bind.bind, Aeneas.Std.bind,
            core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
            at hrun
        | some fillTuple =>
          rcases fillTuple with ⟨filledInput, nextNodePos, nextValuePos⟩
          simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            Aeneas.Std.bind_tc_ok, lift] at hrun
          generalize hhash :
            merkle.fixed_hashv
              (Array.to_slice
                (Array.make 1#usize [Array.to_slice filledInput])) =
              hashResult
          rw [hhash] at hrun
          cases hashResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok digest =>
            simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
            generalize hpush : alloc.vec.Vec.push next digest = pushResult
            rw [hpush] at hrun
            cases pushResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | ok next' =>
              simp only [Aeneas.Std.bind_tc_ok, lift] at hrun
              have hchildren :=
                fixed_fill_radix_children_success_yields_four_steps
                  nodeBytes level present nodePos valuePos input filledInput
                  nextNodePos nextValuePos hnodePos hroom hfill
              exact ⟨{
                present := present
                input := input
                filledInput := filledInput
                nextNodePos := nextNodePos
                nextValuePos := nextValuePos
                digest := digest
                next' := next'
                init_run := hinit
                mask_run := hmask
                fill_run := hfill
                children := Classical.choice hchildren
                hash_run := hhash
                push_run := hpush
                recurse_run := hrun }⟩

/-- Every digest appended by one generated group step is exactly the maintained
model's radix-four hash of the four children selected by that step. -/
theorem GeneratedGroupStep.digest_exact
    {nodeBytes : Slice Std.U8} {level : Slice GeneratedDigest}
    {masks : Slice Std.U8} {maskPos nodePos valuePos : Std.Usize}
    {next finalNext : GeneratedDigestVec}
    {finalNodePos finalValuePos : Std.Usize}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (step : GeneratedGroupStep nodeBytes level masks maskPos nodePos valuePos
      next finalNext finalNodePos finalValuePos) :
    generatedArrayToDigest step.digest =
      (sha256MerkleHashing sha256).radix4Node
        (fun slot => generatedArrayToDigest (step.children.child slot)) := by
  apply step.children.hash_exact sha256 hhash
  · have hinit := step.init_run
    simp [Array.update, core.array.Array.index_mut,
      core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
      List.set] at hinit
    simpa using (congrArg (fun value => value.val[0]!) hinit).symm
  · exact step.hash_run

/-- Complete successful recursion of the generated group helper.  The `done`
constructor is the exact mask-end return; `step` records one source iteration
and the trace of the strictly shorter suffix. -/
inductive GeneratedGroupTrace
    (nodeBytes : Slice Std.U8) (level : Slice GeneratedDigest)
    (masks : Slice Std.U8) :
    Std.Usize → Std.Usize → Std.Usize → GeneratedDigestVec →
      GeneratedDigestVec → Std.Usize → Std.Usize → Prop
  | done (maskPos nodePos valuePos : Std.Usize) (next : GeneratedDigestVec)
      (hdone : masks.val.length ≤ maskPos.val) :
      GeneratedGroupTrace nodeBytes level masks maskPos nodePos valuePos next
        next nodePos valuePos
  | step (maskPos nodePos valuePos : Std.Usize)
      (next finalNext : GeneratedDigestVec)
      (finalNodePos finalValuePos : Std.Usize)
      (hactive : maskPos.val < masks.val.length)
      (head : GeneratedGroupStep nodeBytes level masks maskPos nodePos valuePos
        next finalNext finalNodePos finalValuePos)
      (tail : GeneratedGroupTrace nodeBytes level masks
        (Std.Usize.wrapping_add maskPos 1#usize)
        head.nextNodePos head.nextValuePos head.next'
        finalNext finalNodePos finalValuePos) :
      GeneratedGroupTrace nodeBytes level masks maskPos nodePos valuePos next
        finalNext finalNodePos finalValuePos

/-- Any successful generated group run has an exact finite trace, with one
trace node per mask byte and no omitted or extra group. -/
theorem fixed_hash_radix_groups_success_yields_trace
    (nodeBytes : Slice Std.U8) (level : Slice GeneratedDigest)
    (masks : Slice Std.U8) (maskPos nodePos valuePos : Std.Usize)
    (next finalNext : GeneratedDigestVec)
    (finalNodePos finalValuePos : Std.Usize)
    (hnodePos : nodePos.val ≤ nodeBytes.val.length)
    (hroom : nodeBytes.val.length + 32 < UScalar.size .Usize)
    (hmasksRoom : masks.val.length + 1 < UScalar.size .Usize)
    (hrun :
      merkle.fixed_hash_radix_groups nodeBytes level masks maskPos nodePos
          valuePos next =
        .ok (some (finalNext, finalNodePos, finalValuePos))) :
    Nonempty (GeneratedGroupTrace nodeBytes level masks maskPos nodePos
      valuePos next finalNext finalNodePos finalValuePos) := by
  by_cases hdone : masks.val.length ≤ maskPos.val
  · have hterminal :=
      AspisV5MerkleGeneratedHelperBridge.fixed_hash_radix_groups_done
        nodeBytes level masks maskPos nodePos valuePos next hdone
    rw [hterminal] at hrun
    injection hrun with hsome
    have htriple := Option.some.inj hsome
    have hnext : next = finalNext := congrArg Prod.fst htriple
    have hnode : nodePos = finalNodePos :=
      congrArg (fun value => value.2.1) htriple
    have hvalue : valuePos = finalValuePos :=
      congrArg (fun value => value.2.2) htriple
    subst finalNext
    subst finalNodePos
    subst finalValuePos
    exact ⟨GeneratedGroupTrace.done maskPos nodePos valuePos next hdone⟩
  · have hactive : maskPos.val < masks.val.length := by omega
    let head := Classical.choice
      (fixed_hash_radix_groups_success_step nodeBytes level masks maskPos
        nodePos valuePos next finalNext finalNodePos finalValuePos hactive
        hnodePos hroom hrun)
    have hnextNode := head.children.finalNodePos_le hnodePos
    have hmaskSucc :
        (Std.Usize.wrapping_add maskPos 1#usize).val = maskPos.val + 1 := by
      apply fixed_usize_succ_val_of_room
      omega
    let tail := Classical.choice
      (fixed_hash_radix_groups_success_yields_trace nodeBytes level masks
        (Std.Usize.wrapping_add maskPos 1#usize) head.nextNodePos
        head.nextValuePos head.next' finalNext finalNodePos finalValuePos
        hnextNode hroom hmasksRoom head.recurse_run)
    exact ⟨GeneratedGroupTrace.step maskPos nodePos valuePos next finalNext
      finalNodePos finalValuePos hactive head tail⟩
termination_by masks.val.length - maskPos.val
decreasing_by
  rw [hmaskSucc]
  omega

/-- One present slot of the extracted recursive child helper reads the next
level value, writes it into that slot, advances only the value cursor, and
continues with the following slot. -/
theorem fixed_fill_radix_children_present_step
    (nodeBytes : Slice Std.U8) (level : Slice GeneratedDigest)
    (present : Std.U8) (slot nodePos valuePos : Std.Usize)
    (input input' : GeneratedRadixInput) (value : GeneratedDigest)
    (hslot : slot.val < 4)
    (hpresent :
      present &&& Std.U8.wrapping_shl 1#u8 (usizeShiftCount slot) != 0#u8)
    (hvaluePos : valuePos.val < level.val.length)
    (hvalue : Slice.index_usize level valuePos = .ok value)
    (hwrite : merkle.fixed_write_radix_child input slot value = .ok input') :
    merkle.fixed_fill_radix_children nodeBytes level present slot nodePos
        valuePos input =
      merkle.fixed_fill_radix_children nodeBytes level present
        (Std.Usize.wrapping_add slot 1#usize) nodePos
        (Std.Usize.wrapping_add valuePos 1#usize) input' := by
  rw [merkle.fixed_fill_radix_children.eq_def]
  have hnotDone : ¬ slot ≥ 4#usize := by scalar_tac
  simp only [hnotDone, if_false, lift, Bind.bind, Aeneas.Std.bind]
  rw [if_pos hpresent]
  have hnotPast : ¬ valuePos ≥ Slice.len level := by
    change ¬ valuePos.val ≥ level.val.length
    omega
  simp only [hnotPast, if_false, hvalue, Bind.bind, Aeneas.Std.bind, hwrite]

/-- One absent slot reads exactly the next 32 frontier bytes, writes that
digest into the slot, advances only the frontier cursor, and continues. -/
theorem fixed_fill_radix_children_frontier_step
    (nodeBytes : Slice Std.U8) (level : Slice GeneratedDigest)
    (present : Std.U8) (slot nodePos valuePos : Std.Usize)
    (input input' : GeneratedRadixInput) (value : GeneratedDigest)
    (hslot : slot.val < 4)
    (habsent :
      ¬ (present &&& Std.U8.wrapping_shl 1#u8 (usizeShiftCount slot) !=
        0#u8))
    (hspace :
      ¬ Std.Usize.wrapping_add nodePos 32#usize > Slice.len nodeBytes)
    (hread :
      merkle.fixed_fill_radix_children_loop nodeBytes nodePos
        (Array.repeat 32#usize 0#u8) 0#usize = .ok value)
    (hwrite : merkle.fixed_write_radix_child input slot value = .ok input') :
    merkle.fixed_fill_radix_children nodeBytes level present slot nodePos
        valuePos input =
      merkle.fixed_fill_radix_children nodeBytes level present
        (Std.Usize.wrapping_add slot 1#usize)
        (Std.Usize.wrapping_add nodePos 32#usize) valuePos input' := by
  rw [merkle.fixed_fill_radix_children.eq_def]
  have hnotDone : ¬ slot ≥ 4#usize := by scalar_tac
  simp only [hnotDone, if_false, lift, Bind.bind, Aeneas.Std.bind]
  rw [if_neg habsent]
  simp only [hspace, if_false, hread, hwrite]

/-- A nonterminal group step fills one four-child preimage, hashes that exact
129-byte array, appends the digest, advances the two cursors returned by the
child scan, and recurses at the next mask. -/
theorem fixed_hash_radix_groups_step
    (nodeBytes : Slice Std.U8) (level : Slice GeneratedDigest)
    (masks : Slice Std.U8) (maskPos nodePos valuePos : Std.Usize)
    (next next' : GeneratedDigestVec)
    (input input' : GeneratedRadixInput) (present : Std.U8)
    (nodePos' valuePos' : Std.Usize)
    (digest : GeneratedDigest)
    (hmaskPos : maskPos.val < masks.val.length)
    (hinit :
      Array.update (Array.repeat 129#usize 0#u8) 0#usize merkle.DOM_NODE4 =
        .ok input)
    (hmask : Slice.index_usize masks maskPos = .ok present)
    (hfill :
      merkle.fixed_fill_radix_children nodeBytes level present 0#usize
        nodePos valuePos input = .ok (some (input', nodePos', valuePos')))
    (hhash :
      merkle.fixed_hashv
          (Array.to_slice
            (Array.make 1#usize [Array.to_slice input'])) = .ok digest)
    (hpush : alloc.vec.Vec.push next digest = .ok next') :
    merkle.fixed_hash_radix_groups nodeBytes level masks maskPos nodePos
        valuePos next =
      merkle.fixed_hash_radix_groups nodeBytes level masks
        (Std.Usize.wrapping_add maskPos 1#usize) nodePos' valuePos' next' := by
  rw [merkle.fixed_hash_radix_groups.eq_def]
  have hnotDone : ¬ maskPos ≥ Slice.len masks := by
    change ¬ maskPos.val ≥ masks.val.length
    omega
  simp only [hnotDone, if_false, hinit, hmask, hfill,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch, Bind.bind,
    Aeneas.Std.bind, hhash, hpush, lift]

/-- A nonterminal level step selects exactly one topology mask slice, hashes
all of its groups, requires every current-level value to have been consumed,
swaps the two scratch vectors, and recurses at the next plan level. -/
theorem fixed_hash_radix_levels_step
    (topology : merkle.Radix4BinaryCapTopology)
    (nodeBytes : Slice Std.U8) (planLevel nodePos : Std.Usize)
    (level next nextCleared nextHashed level' next' : GeneratedDigestVec)
    (masksVec : alloc.vec.Vec Std.U8)
    (maskStart maskEnd nodePos' valuePos' : Std.Usize)
    (maskSlice : Slice Std.U8)
    (hplanLevel : planLevel.val < topology.radix_levels.val)
    (hclear : alloc.vec.Vec.clear Global next = .ok nextCleared)
    (hmaskStart :
      Array.index_usize topology.group_offsets planLevel = .ok maskStart)
    (hmaskEnd :
      Array.index_usize topology.group_offsets
        (Std.Usize.wrapping_add planLevel 1#usize) = .ok maskEnd)
    (hmaskSlice :
      alloc.vec.Vec.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
          topology.group_masks { start := maskStart, «end» := maskEnd } =
        .ok maskSlice)
    (hmasksVec :
      alloc.slice.Slice.to_vec core.clone.CloneU8 maskSlice = .ok masksVec)
    (hgroups :
      merkle.fixed_hash_radix_groups nodeBytes (alloc.vec.Vec.deref level)
          (alloc.vec.Vec.deref masksVec) 0#usize nodePos 0#usize nextCleared =
        .ok (some (nextHashed, nodePos', valuePos')))
    (hconsumed : valuePos' = alloc.vec.Vec.len level)
    (hswap : core.mem.swap level nextHashed = (level', next')) :
    merkle.fixed_hash_radix_levels topology nodeBytes planLevel nodePos level
        next =
      merkle.fixed_hash_radix_levels topology nodeBytes
        (Std.Usize.wrapping_add planLevel 1#usize) nodePos' level' next' := by
  rw [merkle.fixed_hash_radix_levels.eq_def]
  have hnotDone : ¬ planLevel ≥ topology.radix_levels := by scalar_tac
  simp only [hnotDone, if_false, hclear, hmaskStart, lift, Bind.bind,
    Aeneas.Std.bind, hmaskEnd, hmaskSlice, hmasksVec, hgroups,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  have hvalueEq :
      (valuePos' != alloc.vec.Vec.len level) = false := by
    simp [hconsumed]
  simp only [hvalueEq, Bool.false_eq_true, if_false, hswap]

end AspisV5MerkleGeneratedRadixBridge
