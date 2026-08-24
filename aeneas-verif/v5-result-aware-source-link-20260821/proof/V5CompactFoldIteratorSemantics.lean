import V5CompactFoldSourceModel

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CompactFoldIteratorSemantics

open V5RelationCompactFoldGenerated
open AspisV5RelationCompactFoldKernelProof

abbrev Iter := core.slice.iter.IterMut

theorem next_in_bounds {T : Type} (iter : Iter T)
    (h : iter.i < iter.slice.len) :
    core.slice.iter.IteratorIterMut.next iter =
      .ok
        (some iter.slice[iter.i],
          { iter with i := iter.i + 1 },
          fun iter' value =>
            match value with
            | none => iter'
            | some value =>
                { iter' with slice := iter'.slice.setAtNat iter.i value }) := by
  unfold core.slice.iter.IteratorIterMut.next
  rw [dif_pos h]
  rfl

theorem next_exhausted {T : Type} (iter : Iter T)
    (h : ¬ iter.i < iter.slice.len) :
    core.slice.iter.IteratorIterMut.next iter =
      .ok (none, iter, fun iter' _ => iter') := by
  unfold core.slice.iter.IteratorIterMut.next
  rw [dif_neg h]

abbrev Raw := V5RelationCompactFoldGenerated.aspis_core.field.QM31
abbrev Prepared :=
  V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier
abbrev Block :=
  V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev BlockIter := core.slice.iter.IterMut Block
abbrev Back := BlockIter → BlockIter
abbrev FoldFlow := ControlFlow (BlockIter × Back × Std.U8) (Std.U8 × Back)

def zeroBodyModel
    (prepared : Array Prepared 3#usize) (iter : BlockIter) (back : Back) :
    Result FoldFlow := do
  let (value, iterAfter, nextBack) ←
    core.slice.iter.IteratorIterMut.next iter
  match value with
  | none => ok (done (0#u8, fun output => back (nextBack output none)))
  | some block =>
      AspisV5RelationCompactFoldKernelProof.continueWith
        iterAfter nextBack back 0#u8
        (AspisV5RelationCompactFoldKernelProof.foldZeroBlock prepared block)

theorem generated_zero_body_eq_model
    (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 prepared iter back 0#u8 =
      zeroBodyModel prepared iter back := by
  unfold zeroBodyModel
  generalize nextRun :
    core.slice.iter.IteratorIterMut.next iter = nextResult
  cases nextResult with
  | fail error =>
      simp only [bind_tc_fail]
      unfold
        V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_fail]
  | div =>
      simp only [bind_tc_div]
      unfold
        V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_div]
  | ok result =>
      rcases result with ⟨value, iterAfter, nextBack⟩
      cases value with
      | none =>
          unfold
            V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
          simp only [nextRun, bind_tc_ok]
      | some block =>
          rw [
            AspisV5RelationCompactFoldKernelProof.extracted_fold_zero_block_exact
              alpha alpha2 alpha3 prepared iter iterAfter nextBack back block
              nextRun,
            AspisV5RelationCompactFoldKernelProof.foldZeroStep_eq_continueWith]
          rfl

def zeroLoopBody (prepared : Array Prepared 3#usize)
    (state : BlockIter × Back × Std.U8) :
    Result (ControlFlow (BlockIter × Back × Std.U8) (Std.U8 × Back)) :=
  zeroBodyModel prepared state.1 state.2.1

def zeroBackN : Nat → Array Prepared 3#usize → BlockIter → Back →
    Result (Std.U8 × Back)
  | 0, _, _, back => ok (0#u8, back)
  | remaining + 1, prepared, iter, back => do
      let (value, iterAfter, nextBack) ←
        core.slice.iter.IteratorIterMut.next iter
      match value with
      | none => fail panic
      | some block =>
          let updated ←
            AspisV5RelationCompactFoldKernelProof.foldZeroBlock prepared block
          zeroBackN remaining prepared iterAfter
            (fun output => back (nextBack output (some updated)))

theorem zero_loop_eq_zeroBackN
    (remaining : Nat) (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back)
    (lengthExact : iter.i + remaining = iter.slice.val.length) :
    Aeneas.Std.loop (zeroLoopBody prepared) (iter, back, 0#u8) =
      zeroBackN remaining prepared iter back := by
  induction remaining generalizing iter back with
  | zero =>
      have exhausted : ¬ iter.i < iter.slice.len := by
        change ¬ iter.i < iter.slice.val.length
        omega
      rw [Aeneas.Std.loop.eq_def]
      simp only [zeroLoopBody, zeroBodyModel, next_exhausted iter exhausted,
        bind_tc_ok, zeroBackN]
  | succ remaining inductionHypothesis =>
      have inBounds : iter.i < iter.slice.len := by
        change iter.i < iter.slice.val.length
        omega
      have nextLength :
          ({ iter with i := iter.i + 1 } : BlockIter).i + remaining =
            ({ iter with i := iter.i + 1 } : BlockIter).slice.val.length := by
        simp only
        omega
      rw [Aeneas.Std.loop.eq_def]
      simp only [zeroLoopBody, zeroBodyModel, zeroBackN,
        next_in_bounds iter inBounds, bind_tc_ok]
      generalize blockRun :
        AspisV5RelationCompactFoldKernelProof.foldZeroBlock prepared
          iter.slice[iter.i] = blockResult
      cases blockResult with
      | fail error =>
          simp only [AspisV5RelationCompactFoldKernelProof.continueWith,
            bind_tc_fail]
      | div =>
          simp only [AspisV5RelationCompactFoldKernelProof.continueWith,
            bind_tc_div]
      | ok updated =>
          simp only [bind_tc_ok]
          exact inductionHypothesis
            ({ iter with i := iter.i + 1 })
            (fun (output : BlockIter) =>
              back
                ((fun (iter' : BlockIter) (value : Option Block) =>
                  match value with
                  | none => iter'
                  | some value =>
                      { iter' with
                        slice := iter'.slice.setAtNat iter.i value })
                output (some updated)))
            nextLength

def generatedZeroLoopBody
    (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (state : BlockIter × Back × Std.U8) :
    Result (ControlFlow (BlockIter × Back × Std.U8) (Std.U8 × Back)) :=
  V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
    alpha alpha2 alpha3 prepared state.1 state.2.1 state.2.2

theorem generated_zero_loop_eq_zeroBackN_aux
    (remaining : Nat) (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back)
    (lengthExact : iter.i + remaining = iter.slice.val.length) :
    Aeneas.Std.loop
        (generatedZeroLoopBody alpha alpha2 alpha3 prepared)
        (iter, back, 0#u8) =
      zeroBackN remaining prepared iter back := by
  induction remaining generalizing iter back with
  | zero =>
      have exhausted : ¬ iter.i < iter.slice.len := by
        change ¬ iter.i < iter.slice.val.length
        omega
      rw [Aeneas.Std.loop.eq_def]
      unfold generatedZeroLoopBody
      rw [generated_zero_body_eq_model]
      simp only [zeroBodyModel, next_exhausted iter exhausted, bind_tc_ok,
        zeroBackN]
  | succ remaining inductionHypothesis =>
      have inBounds : iter.i < iter.slice.len := by
        change iter.i < iter.slice.val.length
        omega
      have nextLength :
          ({ iter with i := iter.i + 1 } : BlockIter).i + remaining =
            ({ iter with i := iter.i + 1 } : BlockIter).slice.val.length := by
        simp only
        omega
      rw [Aeneas.Std.loop.eq_def]
      unfold generatedZeroLoopBody
      rw [generated_zero_body_eq_model]
      simp only [zeroBodyModel, zeroBackN,
        next_in_bounds iter inBounds, bind_tc_ok]
      generalize blockRun :
        AspisV5RelationCompactFoldKernelProof.foldZeroBlock prepared
          iter.slice[iter.i] = blockResult
      cases blockResult with
      | fail error =>
          simp only [AspisV5RelationCompactFoldKernelProof.continueWith,
            bind_tc_fail]
      | div =>
          simp only [AspisV5RelationCompactFoldKernelProof.continueWith,
            bind_tc_div]
      | ok updated =>
          simp only [bind_tc_ok]
          exact inductionHypothesis
            ({ iter with i := iter.i + 1 })
            (fun (output : BlockIter) =>
              back
                ((fun (iter' : BlockIter) (value : Option Block) =>
                  match value with
                  | none => iter'
                  | some value =>
                      { iter' with
                        slice := iter'.slice.setAtNat iter.i value })
                output (some updated)))
            nextLength

theorem generated_zero_loop_eq_zeroBackN
    (remaining : Nat) (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back)
    (lengthExact : iter.i + remaining = iter.slice.val.length) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop
        iter back 0#u8 alpha alpha2 alpha3 prepared =
      zeroBackN remaining prepared iter back := by
  unfold
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop
  exact generated_zero_loop_eq_zeroBackN_aux remaining alpha alpha2 alpha3
    prepared iter back lengthExact

/-! The remaining three released counter values use the same iterator proof.
Only the per-block source transformation changes. -/

def sourceBodyModel
    (folds : Std.U8) (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize) (iter : BlockIter) (back : Back) :
    Result FoldFlow := do
  let (value, iterAfter, nextBack) ←
    core.slice.iter.IteratorIterMut.next iter
  match value with
  | none => ok (done (folds, fun output => back (nextBack output none)))
  | some block =>
      AspisV5RelationCompactFoldKernelProof.continueWith
        iterAfter nextBack back folds
        (V5CompactFoldSource.foldBlock folds alpha alpha2 alpha3 prepared block)

theorem generated_one_body_eq_source
    (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 prepared iter back 1#u8 =
      sourceBodyModel 1#u8 alpha alpha2 alpha3 prepared iter back := by
  unfold sourceBodyModel
  generalize nextRun :
    core.slice.iter.IteratorIterMut.next iter = nextResult
  cases nextResult with
  | fail error =>
      simp only [bind_tc_fail]
      unfold
        V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_fail]
  | div =>
      simp only [bind_tc_div]
      unfold
        V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_div]
  | ok result =>
      rcases result with ⟨value, iterAfter, nextBack⟩
      cases value with
      | none =>
          unfold
            V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
          simp only [nextRun, bind_tc_ok]
      | some block =>
          rw [
            AspisV5RelationCompactFoldKernelProof.extracted_fold_one_block_exact
              alpha alpha2 alpha3 prepared iter iterAfter nextBack back block
              nextRun,
            AspisV5RelationCompactFoldKernelProof.foldOneStep_eq_continueWith]
          rfl

theorem generated_two_body_eq_source
    (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 prepared iter back 2#u8 =
      sourceBodyModel 2#u8 alpha alpha2 alpha3 prepared iter back := by
  unfold sourceBodyModel
  generalize nextRun :
    core.slice.iter.IteratorIterMut.next iter = nextResult
  cases nextResult with
  | fail error =>
      simp only [bind_tc_fail]
      unfold
        V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_fail]
  | div =>
      simp only [bind_tc_div]
      unfold
        V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_div]
  | ok result =>
      rcases result with ⟨value, iterAfter, nextBack⟩
      cases value with
      | none =>
          unfold
            V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
          simp only [nextRun, bind_tc_ok]
      | some block =>
          by_cases even : (block.selector &&& 1#u8) = 0#u8
          · rw [
              AspisV5RelationCompactFoldKernelProof.extracted_fold_two_even_block_exact
                alpha alpha2 alpha3 prepared iter iterAfter nextBack back block
                nextRun even,
              AspisV5RelationCompactFoldKernelProof.foldTwoEvenStep_eq_continueWith]
            change
              AspisV5RelationCompactFoldKernelProof.continueWith
                  iterAfter nextBack back 2#u8
                  (AspisV5RelationCompactFoldKernelProof.foldTwoEvenBlock
                    prepared block) =
                AspisV5RelationCompactFoldKernelProof.continueWith
                  iterAfter nextBack back 2#u8
                  (if (block.selector &&& 1#u8) = 0#u8 then
                    AspisV5RelationCompactFoldKernelProof.foldTwoEvenBlock
                      prepared block
                  else
                    AspisV5RelationCompactFoldKernelProof.foldTwoOddBlock
                      prepared block)
            rw [if_pos even]
          · rw [
              AspisV5RelationCompactFoldKernelProof.extracted_fold_two_odd_block_exact
                alpha alpha2 alpha3 prepared iter iterAfter nextBack back block
                nextRun even,
              AspisV5RelationCompactFoldKernelProof.foldTwoOddStep_eq_continueWith]
            change
              AspisV5RelationCompactFoldKernelProof.continueWith
                  iterAfter nextBack back 2#u8
                  (AspisV5RelationCompactFoldKernelProof.foldTwoOddBlock
                    prepared block) =
                AspisV5RelationCompactFoldKernelProof.continueWith
                  iterAfter nextBack back 2#u8
                  (if (block.selector &&& 1#u8) = 0#u8 then
                    AspisV5RelationCompactFoldKernelProof.foldTwoEvenBlock
                      prepared block
                  else
                    AspisV5RelationCompactFoldKernelProof.foldTwoOddBlock
                      prepared block)
            rw [if_neg even]

private theorem u8_bitand_three_lt_four (value : Std.U8) :
    (value &&& 3#u8).val < 4 := by
  rw [UScalar.val_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem generated_three_body_eq_source
    (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 prepared iter back 3#u8 =
      sourceBodyModel 3#u8 alpha alpha2 alpha3 prepared iter back := by
  unfold sourceBodyModel
  generalize nextRun :
    core.slice.iter.IteratorIterMut.next iter = nextResult
  cases nextResult with
  | fail error =>
      simp only [bind_tc_fail]
      unfold
        V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_fail]
  | div =>
      simp only [bind_tc_div]
      unfold
        V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_div]
  | ok result =>
      rcases result with ⟨value, iterAfter, nextBack⟩
      cases value with
      | none =>
          unfold
            V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
          simp only [nextRun, bind_tc_ok]
      | some block =>
          let pair := Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8
          have pairBound : pair.val < 4 := by
            exact u8_bitand_three_lt_four
              (Std.U8.wrapping_shr block.selector 1#u32)
          have pairCases : pair.val = 0 ∨ pair.val = 1 ∨ pair.val = 2 ∨
              pair.val = 3 := by omega
          rcases pairCases with pairValue | pairValue | pairValue | pairValue
          · have pairExact :
                (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) =
                  0#u8 := by
              apply UScalar.eq_of_val_eq
              simpa [pair] using pairValue
            rw [
              AspisV5RelationCompactFoldKernelProof.extracted_fold_three_pair_zero_exact
                alpha alpha2 alpha3 prepared iter iterAfter nextBack back block
                nextRun pairExact,
              AspisV5RelationCompactFoldKernelProof.foldThreeStep_eq_continueWith]
            have sourceExact :
                V5CompactFoldSource.foldBlock 3#u8 alpha alpha2 alpha3
                    prepared block =
                  AspisV5RelationCompactFoldKernelProof.foldThreeBlock
                    aspis_core.field.QM31.ONE block := by
              have pairExplicit :
                  (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) =
                    @UScalar.mk .U8 (0#8) := pairExact
              unfold V5CompactFoldSource.foldBlock
              change (match
                (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) with
                | 0#uscalar => _ | 1#uscalar => _ | 2#uscalar => _
                | 3#uscalar => _ | _ => _) = _
              rw [pairExplicit]
              split
              · rfl
              · rename_i _ different
                exact ((by decide : (0#u8 : Std.U8) ≠ 1#u8) different).elim
              · rename_i _ different
                exact ((by decide : (0#u8 : Std.U8) ≠ 2#u8) different).elim
              · rename_i _ different
                exact ((by decide : (0#u8 : Std.U8) ≠ 3#u8) different).elim
              · rename_i _ notZero _ _ _
                exact (notZero rfl).elim
            simp only [nextRun, bind_tc_ok]
            rw [sourceExact]
          · have pairExact :
                (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) =
                  1#u8 := by
              apply UScalar.eq_of_val_eq
              simpa [pair] using pairValue
            rw [
              AspisV5RelationCompactFoldKernelProof.extracted_fold_three_pair_one_exact
                alpha alpha2 alpha3 prepared iter iterAfter nextBack back block
                nextRun pairExact,
              AspisV5RelationCompactFoldKernelProof.foldThreeStep_eq_continueWith]
            have sourceExact :
                V5CompactFoldSource.foldBlock 3#u8 alpha alpha2 alpha3
                    prepared block =
                  AspisV5RelationCompactFoldKernelProof.foldThreeBlock
                    alpha3 block := by
              have pairExplicit :
                  (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) =
                    @UScalar.mk .U8 (1#8) := pairExact
              unfold V5CompactFoldSource.foldBlock
              change (match
                (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) with
                | 0#uscalar => _ | 1#uscalar => _ | 2#uscalar => _
                | 3#uscalar => _ | _ => _) = _
              rw [pairExplicit]
              split
              · rename_i _ different
                exact ((by decide : (1#u8 : Std.U8) ≠ 0#u8) different).elim
              · rfl
              · rename_i _ different
                exact ((by decide : (1#u8 : Std.U8) ≠ 2#u8) different).elim
              · rename_i _ different
                exact ((by decide : (1#u8 : Std.U8) ≠ 3#u8) different).elim
              · rename_i _ _ notOne _ _
                exact (notOne rfl).elim
            simp only [nextRun, bind_tc_ok]
            rw [sourceExact]
          · have pairExact :
                (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) =
                  2#u8 := by
              apply UScalar.eq_of_val_eq
              simpa [pair] using pairValue
            rw [
              AspisV5RelationCompactFoldKernelProof.extracted_fold_three_pair_two_exact
                alpha alpha2 alpha3 prepared iter iterAfter nextBack back block
                nextRun pairExact,
              AspisV5RelationCompactFoldKernelProof.foldThreeStep_eq_continueWith]
            have sourceExact :
                V5CompactFoldSource.foldBlock 3#u8 alpha alpha2 alpha3
                    prepared block =
                  AspisV5RelationCompactFoldKernelProof.foldThreeBlock
                    alpha2 block := by
              have pairExplicit :
                  (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) =
                    @UScalar.mk .U8 (2#8) := pairExact
              unfold V5CompactFoldSource.foldBlock
              change (match
                (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) with
                | 0#uscalar => _ | 1#uscalar => _ | 2#uscalar => _
                | 3#uscalar => _ | _ => _) = _
              rw [pairExplicit]
              split
              · rename_i _ different
                exact ((by decide : (2#u8 : Std.U8) ≠ 0#u8) different).elim
              · rename_i _ different
                exact ((by decide : (2#u8 : Std.U8) ≠ 1#u8) different).elim
              · rfl
              · rename_i _ different
                exact ((by decide : (2#u8 : Std.U8) ≠ 3#u8) different).elim
              · rename_i _ _ _ notTwo _
                exact (notTwo rfl).elim
            simp only [nextRun, bind_tc_ok]
            rw [sourceExact]
          · have pairExact :
                (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) =
                  3#u8 := by
              apply UScalar.eq_of_val_eq
              simpa [pair] using pairValue
            rw [
              AspisV5RelationCompactFoldKernelProof.extracted_fold_three_pair_three_exact
                alpha alpha2 alpha3 prepared iter iterAfter nextBack back block
                nextRun pairExact,
              AspisV5RelationCompactFoldKernelProof.foldThreeStep_eq_continueWith]
            have sourceExact :
                V5CompactFoldSource.foldBlock 3#u8 alpha alpha2 alpha3
                    prepared block =
                  AspisV5RelationCompactFoldKernelProof.foldThreeBlock
                    alpha block := by
              have pairExplicit :
                  (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) =
                    @UScalar.mk .U8 (3#8) := pairExact
              unfold V5CompactFoldSource.foldBlock
              change (match
                (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) with
                | 0#uscalar => _ | 1#uscalar => _ | 2#uscalar => _
                | 3#uscalar => _ | _ => _) = _
              rw [pairExplicit]
              split
              · rename_i _ different
                exact ((by decide : (3#u8 : Std.U8) ≠ 0#u8) different).elim
              · rename_i _ different
                exact ((by decide : (3#u8 : Std.U8) ≠ 1#u8) different).elim
              · rename_i _ different
                exact ((by decide : (3#u8 : Std.U8) ≠ 2#u8) different).elim
              · rfl
              · rename_i _ _ _ _ notThree
                exact (notThree rfl).elim
            simp only [nextRun, bind_tc_ok]
            rw [sourceExact]

theorem generated_zero_body_eq_source
    (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 prepared iter back 0#u8 =
      sourceBodyModel 0#u8 alpha alpha2 alpha3 prepared iter back := by
  rw [generated_zero_body_eq_model]
  unfold zeroBodyModel sourceBodyModel
  generalize nextRun :
    core.slice.iter.IteratorIterMut.next iter = nextResult
  cases nextResult with
  | fail error => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]
  | ok result =>
      rcases result with ⟨value, iterAfter, nextBack⟩
      cases value with
      | none => simp only [bind_tc_ok]
      | some block =>
          simp only [bind_tc_ok]
          have sourceExact :
              V5CompactFoldSource.foldBlock 0#u8 alpha alpha2 alpha3
                  prepared block =
                AspisV5RelationCompactFoldKernelProof.foldZeroBlock
                  prepared block := by
            rfl
          rw [sourceExact]

theorem generated_body_eq_source
    (folds : Std.U8) (foldBound : folds.val < 4)
    (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 prepared iter back folds =
      sourceBodyModel folds alpha alpha2 alpha3 prepared iter back := by
  have foldCases : folds.val = 0 ∨ folds.val = 1 ∨ folds.val = 2 ∨
      folds.val = 3 := by omega
  rcases foldCases with foldValue | foldValue | foldValue | foldValue
  · have foldExact : folds = 0#u8 := by
      apply UScalar.eq_of_val_eq
      simpa using foldValue
    subst folds
    exact generated_zero_body_eq_source alpha alpha2 alpha3 prepared iter back
  · have foldExact : folds = 1#u8 := by
      apply UScalar.eq_of_val_eq
      simpa using foldValue
    subst folds
    exact generated_one_body_eq_source alpha alpha2 alpha3 prepared iter back
  · have foldExact : folds = 2#u8 := by
      apply UScalar.eq_of_val_eq
      simpa using foldValue
    subst folds
    exact generated_two_body_eq_source alpha alpha2 alpha3 prepared iter back
  · have foldExact : folds = 3#u8 := by
      apply UScalar.eq_of_val_eq
      simpa using foldValue
    subst folds
    exact generated_three_body_eq_source alpha alpha2 alpha3 prepared iter back

def sourceBackN : Nat → Std.U8 → Raw → Raw → Raw →
    Array Prepared 3#usize → BlockIter → Back → Result (Std.U8 × Back)
  | 0, folds, _, _, _, _, _, back => ok (folds, back)
  | remaining + 1, folds, alpha, alpha2, alpha3, prepared, iter, back => do
      let (value, iterAfter, nextBack) ←
        core.slice.iter.IteratorIterMut.next iter
      match value with
      | none => fail panic
      | some block =>
          let updated ← V5CompactFoldSource.foldBlock folds alpha alpha2
            alpha3 prepared block
          sourceBackN remaining folds alpha alpha2 alpha3 prepared iterAfter
            (fun output => back (nextBack output (some updated)))

theorem generated_source_loop_eq_sourceBackN_aux
    (remaining : Nat) (folds : Std.U8) (foldBound : folds.val < 4)
    (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back)
    (lengthExact : iter.i + remaining = iter.slice.val.length) :
    Aeneas.Std.loop
        (generatedZeroLoopBody alpha alpha2 alpha3 prepared)
        (iter, back, folds) =
      sourceBackN remaining folds alpha alpha2 alpha3 prepared iter back := by
  induction remaining generalizing iter back with
  | zero =>
      have exhausted : ¬ iter.i < iter.slice.len := by
        change ¬ iter.i < iter.slice.val.length
        omega
      rw [Aeneas.Std.loop.eq_def]
      unfold generatedZeroLoopBody
      rw [generated_body_eq_source folds foldBound]
      simp only [sourceBodyModel, next_exhausted iter exhausted, bind_tc_ok,
        sourceBackN]
  | succ remaining inductionHypothesis =>
      have inBounds : iter.i < iter.slice.len := by
        change iter.i < iter.slice.val.length
        omega
      have nextLength :
          ({ iter with i := iter.i + 1 } : BlockIter).i + remaining =
            ({ iter with i := iter.i + 1 } : BlockIter).slice.val.length := by
        simp only
        omega
      rw [Aeneas.Std.loop.eq_def]
      unfold generatedZeroLoopBody
      rw [generated_body_eq_source folds foldBound]
      simp only [sourceBodyModel, sourceBackN,
        next_in_bounds iter inBounds, bind_tc_ok]
      generalize blockRun :
        V5CompactFoldSource.foldBlock folds alpha alpha2 alpha3 prepared
          iter.slice[iter.i] = blockResult
      cases blockResult with
      | fail error =>
          simp only [AspisV5RelationCompactFoldKernelProof.continueWith,
            bind_tc_fail]
      | div =>
          simp only [AspisV5RelationCompactFoldKernelProof.continueWith,
            bind_tc_div]
      | ok updated =>
          simp only [bind_tc_ok]
          exact inductionHypothesis
            ({ iter with i := iter.i + 1 })
            (fun (output : BlockIter) =>
              back
                ((fun (iter' : BlockIter) (value : Option Block) =>
                  match value with
                  | none => iter'
                  | some value =>
                      { iter' with
                        slice := iter'.slice.setAtNat iter.i value })
                output (some updated)))
            nextLength

theorem generated_source_loop_eq_sourceBackN
    (remaining : Nat) (folds : Std.U8) (foldBound : folds.val < 4)
    (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back)
    (lengthExact : iter.i + remaining = iter.slice.val.length) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop
        iter back folds alpha alpha2 alpha3 prepared =
      sourceBackN remaining folds alpha alpha2 alpha3 prepared iter back := by
  unfold
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop
  exact generated_source_loop_eq_sourceBackN_aux remaining folds foldBound
    alpha alpha2 alpha3 prepared iter back lengthExact

#print axioms generated_one_body_eq_source
#print axioms generated_two_body_eq_source
#print axioms generated_three_body_eq_source
#print axioms generated_body_eq_source
#print axioms generated_source_loop_eq_sourceBackN

end V5CompactFoldIteratorSemantics
