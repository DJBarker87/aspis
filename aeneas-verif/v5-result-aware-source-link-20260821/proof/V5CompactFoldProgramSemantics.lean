import V5CompactFoldSourceUnroll
import V5CompactFoldStateSemantics

/-!
# Exact ten-block compact fold program

This module lifts the arbitrary-input block theorems to the complete extracted
`CompactBTerminalWeights::fold` program.  The square, multiplication and three
prepared-cache constructions are derived here from the generated field code,
before the ten fixed block calls are composed.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5CompactFoldProgramSemantics

open V5RelationCompactFoldGenerated
open AspisV5RelationCompactFoldFieldProjection
open AspisV5RelationCompactFoldPreparedSum
open AspisV5CompactFoldStateSemantics

abbrev Raw := aspis_core.field.QM31
abbrev Prepared := aspis_core.field.PreparedQm31Multiplier
abbrev Block := v5_cu_probe.CompactBTerminalBlock
abbrev State := v5_cu_probe.CompactBTerminalWeights
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact

abbrev foldCounterZero : Std.U8 := 0#8#uscalar
abbrev foldCounterOne : Std.U8 := 1#8#uscalar
abbrev foldCounterTwo : Std.U8 := 2#8#uscalar
abbrev foldCounterThree : Std.U8 := 3#8#uscalar

local instance : Inhabited Raw := ⟨aspis_core.field.QM31.ZERO⟩
local instance : Inhabited Prepared :=
  ⟨⟨Array.repeat 3#usize (Array.repeat 3#usize 0#u32)⟩⟩
local instance : Inhabited Block :=
  ⟨{ scale := aspis_core.field.QM31.ZERO
     power_lo := aspis_core.field.QM31.ZERO
     power_hi := aspis_core.field.QM31.ZERO
     selector := 0#u8 }⟩

private theorem div_two_div_two (value : K) :
    value / 2 / 2 = value / 4 := by
  have twoNeZero : (2 : K) ≠ 0 := by decide
  have fourNeZero : (4 : K) ≠ 0 := by decide
  field_simp
  ring

private theorem list_get_eq_bang
    {T : Type} [Inhabited T] (values : List T) (index : Nat)
    (bound : index < values.length) :
    values[index]'bound = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [bound]

private theorem foldBlock_zero_exact
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (block : Block) :
    V5CompactFoldSource.foldBlock foldCounterZero alpha alpha2 alpha3 prepared block =
      AspisV5RelationCompactFoldKernelProof.foldZeroBlock prepared block := by
  exact V5CompactFoldSource.foldBlock.eq_1 alpha alpha2 alpha3 prepared block

private theorem foldBlock_one_exact
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (block : Block) :
    V5CompactFoldSource.foldBlock foldCounterOne alpha alpha2 alpha3 prepared block =
      AspisV5RelationCompactFoldKernelProof.foldOneBlock prepared block := by
  exact V5CompactFoldSource.foldBlock.eq_2 alpha alpha2 alpha3 prepared block

private theorem foldBlock_two_even_exact
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (block : Block) (even : block.selector &&& 1#u8 = 0#u8) :
    V5CompactFoldSource.foldBlock foldCounterTwo alpha alpha2 alpha3 prepared block =
      AspisV5RelationCompactFoldKernelProof.foldTwoEvenBlock prepared block := by
  rw [V5CompactFoldSource.foldBlock.eq_3, if_pos even]

private theorem foldBlock_two_odd_exact
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (block : Block) (odd : block.selector &&& 1#u8 ≠ 0#u8) :
    V5CompactFoldSource.foldBlock foldCounterTwo alpha alpha2 alpha3 prepared block =
      AspisV5RelationCompactFoldKernelProof.foldTwoOddBlock prepared block := by
  rw [V5CompactFoldSource.foldBlock.eq_3, if_neg odd]

private theorem foldBlock_three_zero_exact
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (block : Block)
    (selected : Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 =
      (0#8#uscalar : Std.U8)) :
    V5CompactFoldSource.foldBlock foldCounterThree alpha alpha2 alpha3 prepared block =
      AspisV5RelationCompactFoldKernelProof.foldThreeBlock
        aspis_core.field.QM31.ONE block := by
  rw [V5CompactFoldSource.foldBlock.eq_4, selected]
  rfl

private theorem foldBlock_three_one_exact
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (block : Block)
    (selected : Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 =
      (1#8#uscalar : Std.U8)) :
    V5CompactFoldSource.foldBlock foldCounterThree alpha alpha2 alpha3 prepared block =
      AspisV5RelationCompactFoldKernelProof.foldThreeBlock alpha3 block := by
  rw [V5CompactFoldSource.foldBlock.eq_4, selected]
  rfl

private theorem foldBlock_three_two_exact
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (block : Block)
    (selected : Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 =
      (2#8#uscalar : Std.U8)) :
    V5CompactFoldSource.foldBlock foldCounterThree alpha alpha2 alpha3 prepared block =
      AspisV5RelationCompactFoldKernelProof.foldThreeBlock alpha2 block := by
  rw [V5CompactFoldSource.foldBlock.eq_4, selected]
  rfl

private theorem foldBlock_three_three_exact
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (block : Block)
    (selected : Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8 =
      (3#8#uscalar : Std.U8)) :
    V5CompactFoldSource.foldBlock foldCounterThree alpha alpha2 alpha3 prepared block =
      AspisV5RelationCompactFoldKernelProof.foldThreeBlock alpha block := by
  rw [V5CompactFoldSource.foldBlock.eq_4, selected]
  rfl

private theorem array_index_run
    {T : Type} [Inhabited T] {count : Std.Usize}
    (values : Array T count) (index : Std.Usize)
    (hindex : index.val < count.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueExact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have listBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have getExact : values.val[index.val] = values.val[index.val]! := by
    exact list_get_eq_bang values.val index.val listBound
  simpa [valueExact, getExact] using run

structure PreparedSetup (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize) : Prop where
  alpha2Canonical : Canonical alpha2
  alpha3Canonical : Canonical alpha3
  alpha2Exact : toK alpha2 = toK alpha ^ 2
  alpha3Exact : toK alpha3 = toK alpha ^ 3
  represented : PreparedTriple prepared alpha3 alpha2 alpha

/-- The setup at the head of every extracted fold call is exact for arbitrary
canonical `alpha`: one square, one multiply, then three generated cache
constructors in the source order. -/
theorem prepared_setup_exists (alpha : Raw) (alphaCanonical : Canonical alpha) :
    ∃ alpha2 alpha3 : Raw, ∃ prepared0 prepared1 prepared2 : Prepared,
      aspis_core.field.QM31.square alpha = ok alpha2 ∧
      aspis_core.field.QM31.mul alpha2 alpha = ok alpha3 ∧
      aspis_core.field.PreparedQm31Multiplier.new alpha3 = ok prepared0 ∧
      aspis_core.field.PreparedQm31Multiplier.new alpha2 = ok prepared1 ∧
      aspis_core.field.PreparedQm31Multiplier.new alpha = ok prepared2 ∧
      PreparedSetup alpha alpha2 alpha3
        (Array.make 3#usize [prepared0, prepared1, prepared2]) := by
  obtain ⟨alpha2, alpha2Run, _, _⟩ :=
    generated_qm31_square_corresponds alpha alphaCanonical
  have alpha2Sem := square_run_exact alpha alpha2 alphaCanonical alpha2Run
  obtain ⟨alpha3, alpha3Run, _, _⟩ :=
    generated_qm31_mul_corresponds alpha2 alpha alpha2Sem.1 alphaCanonical
  have alpha3Sem := mul_run_exact alpha2 alpha alpha3
    alpha2Sem.1 alphaCanonical alpha3Run
  obtain ⟨prepared0, prepared0Run, prepared0Rep⟩ :=
    generated_prepared_new_establishes alpha3 alpha3Sem.1
  obtain ⟨prepared1, prepared1Run, prepared1Rep⟩ :=
    generated_prepared_new_establishes alpha2 alpha2Sem.1
  obtain ⟨prepared2, prepared2Run, prepared2Rep⟩ :=
    generated_prepared_new_establishes alpha alphaCanonical
  refine ⟨alpha2, alpha3, prepared0, prepared1, prepared2,
    alpha2Run, alpha3Run, prepared0Run, prepared1Run, prepared2Run, ?_⟩
  refine {
    alpha2Canonical := alpha2Sem.1
    alpha3Canonical := alpha3Sem.1
    alpha2Exact := alpha2Sem.2
    alpha3Exact := ?_
    represented := ?_ }
  · rw [alpha3Sem.2, alpha2Sem.2]
    ring
  · exact ⟨by simpa [Array.make] using prepared0Rep,
      by simpa [Array.make] using prepared1Rep,
      by simpa [Array.make] using prepared2Rep⟩

structure AcceptedUnrolledFoldTrace (state : State) (alpha : Raw)
    (output : State) : Type where
  alpha2 : Raw
  alpha3 : Raw
  prepared0 : Prepared
  prepared1 : Prepared
  prepared2 : Prepared
  setup : PreparedSetup alpha alpha2 alpha3
    (Array.make 3#usize [prepared0, prepared1, prepared2])
  block0 : Block
  block1 : Block
  block2 : Block
  block3 : Block
  block4 : Block
  block5 : Block
  block6 : Block
  block7 : Block
  block8 : Block
  block9 : Block
  blockRun0 : V5CompactFoldSource.foldBlock state.folds alpha alpha2 alpha3
    (Array.make 3#usize [prepared0, prepared1, prepared2])
    state.blocks.val[(0#usize).val]! = ok block0
  blockRun1 : V5CompactFoldSource.foldBlock state.folds alpha alpha2 alpha3
    (Array.make 3#usize [prepared0, prepared1, prepared2])
    state.blocks.val[(1#usize).val]! = ok block1
  blockRun2 : V5CompactFoldSource.foldBlock state.folds alpha alpha2 alpha3
    (Array.make 3#usize [prepared0, prepared1, prepared2])
    state.blocks.val[(2#usize).val]! = ok block2
  blockRun3 : V5CompactFoldSource.foldBlock state.folds alpha alpha2 alpha3
    (Array.make 3#usize [prepared0, prepared1, prepared2])
    state.blocks.val[(3#usize).val]! = ok block3
  blockRun4 : V5CompactFoldSource.foldBlock state.folds alpha alpha2 alpha3
    (Array.make 3#usize [prepared0, prepared1, prepared2])
    state.blocks.val[(4#usize).val]! = ok block4
  blockRun5 : V5CompactFoldSource.foldBlock state.folds alpha alpha2 alpha3
    (Array.make 3#usize [prepared0, prepared1, prepared2])
    state.blocks.val[(5#usize).val]! = ok block5
  blockRun6 : V5CompactFoldSource.foldBlock state.folds alpha alpha2 alpha3
    (Array.make 3#usize [prepared0, prepared1, prepared2])
    state.blocks.val[(6#usize).val]! = ok block6
  blockRun7 : V5CompactFoldSource.foldBlock state.folds alpha alpha2 alpha3
    (Array.make 3#usize [prepared0, prepared1, prepared2])
    state.blocks.val[(7#usize).val]! = ok block7
  blockRun8 : V5CompactFoldSource.foldBlock state.folds alpha alpha2 alpha3
    (Array.make 3#usize [prepared0, prepared1, prepared2])
    state.blocks.val[(8#usize).val]! = ok block8
  blockRun9 : V5CompactFoldSource.foldBlock state.folds alpha alpha2 alpha3
    (Array.make 3#usize [prepared0, prepared1, prepared2])
    state.blocks.val[(9#usize).val]! = ok block9
  deltaFactor : Raw
  deltaFactorRun :
    (match state.folds with
      | 0#uscalar => ok aspis_core.field.QM31.ONE
      | 1#uscalar => ok aspis_core.field.QM31.ONE
      | 2#uscalar => ok alpha2
      | 3#uscalar => ok alpha
      | _ => fail panic) = ok deltaFactor
  deltaHalf : Raw
  deltaHalfRun : aspis_core.field.QM31.half deltaFactor = ok deltaHalf
  deltaQuarter : Raw
  deltaQuarterRun : aspis_core.field.QM31.half deltaHalf = ok deltaQuarter
  deltaScale : Raw
  deltaScaleRun : aspis_core.field.QM31.mul state.delta_scale deltaQuarter =
    ok deltaScale
  outputExact : output = {
    blocks := Array.make 10#usize [block0, block1, block2, block3, block4,
      block5, block6, block7, block8, block9]
    delta_scale := deltaScale
    folds := Std.U8.wrapping_add state.folds 1#u8 }

private structure AcceptedDeltaTail (state output : State)
    (blocks : Array Block 10#usize) (deltaFactor : Raw) : Type where
  deltaHalf : Raw
  deltaHalfRun : aspis_core.field.QM31.half deltaFactor = ok deltaHalf
  deltaQuarter : Raw
  deltaQuarterRun : aspis_core.field.QM31.half deltaHalf = ok deltaQuarter
  deltaScale : Raw
  deltaScaleRun : aspis_core.field.QM31.mul state.delta_scale deltaQuarter =
    ok deltaScale
  outputExact : output = {
    blocks := blocks
    delta_scale := deltaScale
    folds := Std.U8.wrapping_add state.folds 1#u8 }

private theorem accepted_delta_tail
    (state output : State) (blocks : Array Block 10#usize)
    (deltaFactor : Raw)
    (run : (do
      let deltaHalf <- aspis_core.field.QM31.half deltaFactor
      let deltaQuarter <- aspis_core.field.QM31.half deltaHalf
      let deltaScale <- aspis_core.field.QM31.mul state.delta_scale deltaQuarter
      let folds <- lift (Std.U8.wrapping_add state.folds 1#u8)
      ok { blocks, delta_scale := deltaScale, folds }) = ok output) :
    Nonempty (AcceptedDeltaTail state output blocks deltaFactor) := by
  generalize deltaHalfRun :
    aspis_core.field.QM31.half deltaFactor = deltaHalfResult at run
  cases deltaHalfResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok deltaHalf =>
    simp only [bind_tc_ok] at run
    generalize deltaQuarterRun :
      aspis_core.field.QM31.half deltaHalf = deltaQuarterResult at run
    cases deltaQuarterResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
    | div => simp [Bind.bind, Aeneas.Std.bind] at run
    | ok deltaQuarter =>
      simp only [bind_tc_ok] at run
      generalize deltaScaleRun :
        aspis_core.field.QM31.mul state.delta_scale deltaQuarter =
          deltaScaleResult at run
      cases deltaScaleResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok deltaScale =>
        simp only [bind_tc_ok, Aeneas.Std.lift] at run
        cases run
        exact ⟨{
          deltaHalf, deltaHalfRun, deltaQuarter, deltaQuarterRun,
          deltaScale, deltaScaleRun, outputExact := rfl }⟩

/-- Any successful explicit ten-block run exposes every successful generated
sub-call from that same run. -/
theorem accepted_unrolled_fold_trace
    (state : State) (alpha : Raw) (output : State)
    (alphaCanonical : Canonical alpha)
    (run : V5CompactFoldSource.unrolledFold state alpha = ok output) :
    Nonempty (AcceptedUnrolledFoldTrace state alpha output) := by
  obtain ⟨alpha2, alpha3, prepared0, prepared1, prepared2,
      alpha2Run, alpha3Run, prepared0Run, prepared1Run, prepared2Run,
      setup⟩ := prepared_setup_exists alpha alphaCanonical
  unfold V5CompactFoldSource.unrolledFold at run
  rw [alpha2Run] at run
  simp only [bind_tc_ok] at run
  rw [alpha3Run] at run
  simp only [bind_tc_ok] at run
  rw [prepared0Run] at run
  simp only [bind_tc_ok] at run
  rw [prepared1Run] at run
  simp only [bind_tc_ok] at run
  rw [prepared2Run] at run
  simp only [bind_tc_ok] at run
  rw [array_index_run state.blocks 0#usize (by decide),
    array_index_run state.blocks 1#usize (by decide),
    array_index_run state.blocks 2#usize (by decide),
    array_index_run state.blocks 3#usize (by decide),
    array_index_run state.blocks 4#usize (by decide),
    array_index_run state.blocks 5#usize (by decide),
    array_index_run state.blocks 6#usize (by decide),
    array_index_run state.blocks 7#usize (by decide),
    array_index_run state.blocks 8#usize (by decide),
    array_index_run state.blocks 9#usize (by decide)] at run
  simp only [bind_tc_ok] at run
  generalize blockRun0 : V5CompactFoldSource.foldBlock state.folds alpha
    alpha2 alpha3 (Array.make 3#usize [prepared0, prepared1, prepared2])
    state.blocks.val[(0#usize).val]! = blockResult0 at run
  cases blockResult0 with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok block0 =>
    simp only [bind_tc_ok] at run
    generalize blockRun1 : V5CompactFoldSource.foldBlock state.folds alpha
      alpha2 alpha3 (Array.make 3#usize [prepared0, prepared1, prepared2])
      state.blocks.val[(1#usize).val]! = blockResult1 at run
    cases blockResult1 with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
    | div => simp [Bind.bind, Aeneas.Std.bind] at run
    | ok block1 =>
      simp only [bind_tc_ok] at run
      generalize blockRun2 : V5CompactFoldSource.foldBlock state.folds alpha
        alpha2 alpha3 (Array.make 3#usize [prepared0, prepared1, prepared2])
        state.blocks.val[(2#usize).val]! = blockResult2 at run
      cases blockResult2 with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok block2 =>
        simp only [bind_tc_ok] at run
        generalize blockRun3 : V5CompactFoldSource.foldBlock state.folds alpha
          alpha2 alpha3 (Array.make 3#usize [prepared0, prepared1, prepared2])
          state.blocks.val[(3#usize).val]! = blockResult3 at run
        cases blockResult3 with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
        | div => simp [Bind.bind, Aeneas.Std.bind] at run
        | ok block3 =>
          simp only [bind_tc_ok] at run
          generalize blockRun4 : V5CompactFoldSource.foldBlock state.folds alpha
            alpha2 alpha3 (Array.make 3#usize [prepared0, prepared1, prepared2])
            state.blocks.val[(4#usize).val]! = blockResult4 at run
          cases blockResult4 with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
          | div => simp [Bind.bind, Aeneas.Std.bind] at run
          | ok block4 =>
            simp only [bind_tc_ok] at run
            generalize blockRun5 : V5CompactFoldSource.foldBlock state.folds alpha
              alpha2 alpha3 (Array.make 3#usize [prepared0, prepared1, prepared2])
              state.blocks.val[(5#usize).val]! = blockResult5 at run
            cases blockResult5 with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
            | div => simp [Bind.bind, Aeneas.Std.bind] at run
            | ok block5 =>
              simp only [bind_tc_ok] at run
              generalize blockRun6 : V5CompactFoldSource.foldBlock state.folds alpha
                alpha2 alpha3 (Array.make 3#usize [prepared0, prepared1, prepared2])
                state.blocks.val[(6#usize).val]! = blockResult6 at run
              cases blockResult6 with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
              | div => simp [Bind.bind, Aeneas.Std.bind] at run
              | ok block6 =>
                simp only [bind_tc_ok] at run
                generalize blockRun7 : V5CompactFoldSource.foldBlock state.folds alpha
                  alpha2 alpha3 (Array.make 3#usize [prepared0, prepared1, prepared2])
                  state.blocks.val[(7#usize).val]! = blockResult7 at run
                cases blockResult7 with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                | div => simp [Bind.bind, Aeneas.Std.bind] at run
                | ok block7 =>
                  simp only [bind_tc_ok] at run
                  generalize blockRun8 : V5CompactFoldSource.foldBlock state.folds alpha
                    alpha2 alpha3 (Array.make 3#usize [prepared0, prepared1, prepared2])
                    state.blocks.val[(8#usize).val]! = blockResult8 at run
                  cases blockResult8 with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                  | div => simp [Bind.bind, Aeneas.Std.bind] at run
                  | ok block8 =>
                    simp only [bind_tc_ok] at run
                    generalize blockRun9 : V5CompactFoldSource.foldBlock state.folds alpha
                      alpha2 alpha3 (Array.make 3#usize [prepared0, prepared1, prepared2])
                      state.blocks.val[(9#usize).val]! = blockResult9 at run
                    cases blockResult9 with
                    | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                    | div => simp [Bind.bind, Aeneas.Std.bind] at run
                    | ok block9 =>
                      simp only [bind_tc_ok] at run
                      let blocks := Array.make 10#usize
                        [block0, block1, block2, block3, block4,
                          block5, block6, block7, block8, block9]
                      let finish (deltaFactor : Raw)
                          (deltaFactorRun :
                            (match state.folds with
                              | 0#uscalar => ok aspis_core.field.QM31.ONE
                              | 1#uscalar => ok aspis_core.field.QM31.ONE
                              | 2#uscalar => ok alpha2
                              | 3#uscalar => ok alpha
                              | _ => fail panic) = ok deltaFactor)
                          (tail : AcceptedDeltaTail state output blocks deltaFactor) :
                          Nonempty (AcceptedUnrolledFoldTrace state alpha output) :=
                        ⟨{
                          alpha2, alpha3, prepared0, prepared1, prepared2,
                          setup, block0, block1, block2, block3, block4,
                          block5, block6, block7, block8, block9,
                          blockRun0, blockRun1, blockRun2, blockRun3,
                          blockRun4, blockRun5, blockRun6, blockRun7,
                          blockRun8, blockRun9, deltaFactor, deltaFactorRun,
                          deltaHalf := tail.deltaHalf,
                          deltaHalfRun := tail.deltaHalfRun,
                          deltaQuarter := tail.deltaQuarter,
                          deltaQuarterRun := tail.deltaQuarterRun,
                          deltaScale := tail.deltaScale,
                          deltaScaleRun := tail.deltaScaleRun,
                          outputExact := by simpa [blocks] using tail.outputExact }⟩
                      split at run
                      · obtain ⟨tail⟩ := accepted_delta_tail state output blocks
                          aspis_core.field.QM31.ONE (by simpa [blocks] using run)
                        exact finish aspis_core.field.QM31.ONE (by simp_all) tail
                      · obtain ⟨tail⟩ := accepted_delta_tail state output blocks
                          aspis_core.field.QM31.ONE (by simpa [blocks] using run)
                        exact finish aspis_core.field.QM31.ONE (by simp_all) tail
                      · obtain ⟨tail⟩ := accepted_delta_tail state output blocks
                          alpha2 (by simpa [blocks] using run)
                        exact finish alpha2 (by simp_all) tail
                      · obtain ⟨tail⟩ := accepted_delta_tail state output blocks
                          alpha (by simpa [blocks] using run)
                        exact finish alpha (by simp_all) tail
                      · simp at run

def traceBlocks {state : State} {alpha : Raw} {output : State}
    (trace : AcceptedUnrolledFoldTrace state alpha output) : Array Block 10#usize :=
  Array.make 10#usize [trace.block0, trace.block1, trace.block2, trace.block3,
    trace.block4, trace.block5, trace.block6, trace.block7, trace.block8,
    trace.block9]

def traceBlock {state : State} {alpha : Raw} {output : State}
    (trace : AcceptedUnrolledFoldTrace state alpha output) (index : Fin 10) :
    Block := (traceBlocks trace).val[index.val]!

theorem trace_block_run {state : State} {alpha : Raw} {output : State}
    (trace : AcceptedUnrolledFoldTrace state alpha output) (index : Fin 10) :
    V5CompactFoldSource.foldBlock state.folds alpha trace.alpha2 trace.alpha3
      (Array.make 3#usize [trace.prepared0, trace.prepared1, trace.prepared2])
      state.blocks.val[index.val]! = ok (traceBlock trace index) := by
  fin_cases index
  · simpa [traceBlock, traceBlocks, Array.make] using trace.blockRun0
  · simpa [traceBlock, traceBlocks, Array.make] using trace.blockRun1
  · simpa [traceBlock, traceBlocks, Array.make] using trace.blockRun2
  · simpa [traceBlock, traceBlocks, Array.make] using trace.blockRun3
  · simpa [traceBlock, traceBlocks, Array.make] using trace.blockRun4
  · simpa [traceBlock, traceBlocks, Array.make] using trace.blockRun5
  · simpa [traceBlock, traceBlocks, Array.make] using trace.blockRun6
  · simpa [traceBlock, traceBlocks, Array.make] using trace.blockRun7
  · simpa [traceBlock, traceBlocks, Array.make] using trace.blockRun8
  · simpa [traceBlock, traceBlocks, Array.make] using trace.blockRun9

def ReleasedSelectors (state : State) : Prop :=
  ∀ index : Fin 10,
    (state.blocks.val[index.val]!).selector.val =
      AspisV5CompactTerminal.blockSelector index

private theorem released_selector_eq
    {state : State} (selectors : ReleasedSelectors state)
    (index : Fin 10) (expected : Std.U8)
    (expectedExact : expected.val =
      AspisV5CompactTerminal.blockSelector index) :
    (state.blocks.val[index.val]!).selector = expected := by
  apply UScalar.eq_of_val_eq
  exact (selectors index).trans expectedExact.symm

private theorem optimizedState_ext
    {left right : AspisV5CompactTerminalOptimized.OptimizedState K}
    (blocks : left.blocks = right.blocks)
    (delta : left.deltaScale = right.deltaScale) : left = right := by
  cases left
  cases right
  simp_all

/-- Assemble ten checked block projections and one checked delta projection
into the complete output state. -/
theorem trace_output_corresponds
    {state : State} {alpha : Raw} {output : State}
    (trace : AcceptedUnrolledFoldTrace state alpha output)
    (target : AspisV5CompactTerminalOptimized.OptimizedState K)
    (blockCanonical : ∀ index : Fin 10, CanonicalBlock (traceBlock trace index))
    (blockExact : ∀ index : Fin 10,
      projectBlock (traceBlock trace index) = target.blocks index)
    (deltaCanonical : Canonical trace.deltaScale)
    (deltaExact : toK trace.deltaScale = target.deltaScale) :
    CanonicalState output ∧ projectState output = target := by
  constructor
  · rw [trace.outputExact]
    constructor
    · intro index
      simpa [traceBlock, traceBlocks, Array.make] using blockCanonical index
    · exact deltaCanonical
  · rw [trace.outputExact]
    apply optimizedState_ext
    · funext index
      simpa [projectState, traceBlock, traceBlocks, Array.make] using
        blockExact index
    · simpa [projectState] using deltaExact

theorem releasedSelectors_of_projection
    {output : State}
    (target : AspisV5CompactTerminalOptimized.OptimizedState K)
    (projection : projectState output = target)
    (targetSelectors : ∀ index : Fin 10,
      (target.blocks index).selector = AspisV5CompactTerminal.blockSelector index) :
    ReleasedSelectors output := by
  intro index
  have atIndex := congrArg
    (fun state => (state.blocks index).selector) projection
  change ((projectState output).blocks index).selector = _
  rw [atIndex]
  exact targetSelectors index

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
theorem unrolled_fold_zero_corresponds
    (state : State) (alpha : Raw) (output : State)
    (stateCanonical : CanonicalState state)
    (selectors : ReleasedSelectors state)
    (alphaCanonical : Canonical alpha)
    (foldExact : state.folds = foldCounterZero)
    (run : V5CompactFoldSource.unrolledFold state alpha = ok output) :
    CanonicalState output ∧ ReleasedSelectors output ∧
      output.folds.val = 1 ∧
      projectState output =
        AspisV5CompactTerminalOptimized.optimizedFoldZero
          (toK alpha) (projectState state) := by
  obtain ⟨trace⟩ := accepted_unrolled_fold_trace state alpha output
    alphaCanonical run
  let prepared := Array.make 3#usize
    [trace.prepared0, trace.prepared1, trace.prepared2]
  have blockRun0 := trace.blockRun0
  have blockRun1 := trace.blockRun1
  have blockRun2 := trace.blockRun2
  have blockRun3 := trace.blockRun3
  have blockRun4 := trace.blockRun4
  have blockRun5 := trace.blockRun5
  have blockRun6 := trace.blockRun6
  have blockRun7 := trace.blockRun7
  have blockRun8 := trace.blockRun8
  have blockRun9 := trace.blockRun9
  rw [foldExact] at blockRun0
  rw [foldExact] at blockRun1
  rw [foldExact] at blockRun2
  rw [foldExact] at blockRun3
  rw [foldExact] at blockRun4
  rw [foldExact] at blockRun5
  rw [foldExact] at blockRun6
  rw [foldExact] at blockRun7
  rw [foldExact] at blockRun8
  rw [foldExact] at blockRun9
  rw [foldBlock_zero_exact] at blockRun0
  rw [foldBlock_zero_exact] at blockRun1
  rw [foldBlock_zero_exact] at blockRun2
  rw [foldBlock_zero_exact] at blockRun3
  rw [foldBlock_zero_exact] at blockRun4
  rw [foldBlock_zero_exact] at blockRun5
  rw [foldBlock_zero_exact] at blockRun6
  rw [foldBlock_zero_exact] at blockRun7
  rw [foldBlock_zero_exact] at blockRun8
  rw [foldBlock_zero_exact] at blockRun9
  have blockSem0 := foldZeroBlock_corresponds prepared alpha trace.alpha2
    trace.alpha3 state.blocks.val[0]! trace.block0 alphaCanonical
    trace.setup.alpha2Canonical trace.setup.alpha3Canonical
    trace.setup.alpha2Exact trace.setup.alpha3Exact trace.setup.represented
    (stateCanonical.1 0) (by simpa [prepared] using blockRun0)
  have blockSem1 := foldZeroBlock_corresponds prepared alpha trace.alpha2
    trace.alpha3 state.blocks.val[1]! trace.block1 alphaCanonical
    trace.setup.alpha2Canonical trace.setup.alpha3Canonical
    trace.setup.alpha2Exact trace.setup.alpha3Exact trace.setup.represented
    (stateCanonical.1 1) (by simpa [prepared] using blockRun1)
  have blockSem2 := foldZeroBlock_corresponds prepared alpha trace.alpha2
    trace.alpha3 state.blocks.val[2]! trace.block2 alphaCanonical
    trace.setup.alpha2Canonical trace.setup.alpha3Canonical
    trace.setup.alpha2Exact trace.setup.alpha3Exact trace.setup.represented
    (stateCanonical.1 2) (by simpa [prepared] using blockRun2)
  have blockSem3 := foldZeroBlock_corresponds prepared alpha trace.alpha2
    trace.alpha3 state.blocks.val[3]! trace.block3 alphaCanonical
    trace.setup.alpha2Canonical trace.setup.alpha3Canonical
    trace.setup.alpha2Exact trace.setup.alpha3Exact trace.setup.represented
    (stateCanonical.1 3) (by simpa [prepared] using blockRun3)
  have blockSem4 := foldZeroBlock_corresponds prepared alpha trace.alpha2
    trace.alpha3 state.blocks.val[4]! trace.block4 alphaCanonical
    trace.setup.alpha2Canonical trace.setup.alpha3Canonical
    trace.setup.alpha2Exact trace.setup.alpha3Exact trace.setup.represented
    (stateCanonical.1 4) (by simpa [prepared] using blockRun4)
  have blockSem5 := foldZeroBlock_corresponds prepared alpha trace.alpha2
    trace.alpha3 state.blocks.val[5]! trace.block5 alphaCanonical
    trace.setup.alpha2Canonical trace.setup.alpha3Canonical
    trace.setup.alpha2Exact trace.setup.alpha3Exact trace.setup.represented
    (stateCanonical.1 5) (by simpa [prepared] using blockRun5)
  have blockSem6 := foldZeroBlock_corresponds prepared alpha trace.alpha2
    trace.alpha3 state.blocks.val[6]! trace.block6 alphaCanonical
    trace.setup.alpha2Canonical trace.setup.alpha3Canonical
    trace.setup.alpha2Exact trace.setup.alpha3Exact trace.setup.represented
    (stateCanonical.1 6) (by simpa [prepared] using blockRun6)
  have blockSem7 := foldZeroBlock_corresponds prepared alpha trace.alpha2
    trace.alpha3 state.blocks.val[7]! trace.block7 alphaCanonical
    trace.setup.alpha2Canonical trace.setup.alpha3Canonical
    trace.setup.alpha2Exact trace.setup.alpha3Exact trace.setup.represented
    (stateCanonical.1 7) (by simpa [prepared] using blockRun7)
  have blockSem8 := foldZeroBlock_corresponds prepared alpha trace.alpha2
    trace.alpha3 state.blocks.val[8]! trace.block8 alphaCanonical
    trace.setup.alpha2Canonical trace.setup.alpha3Canonical
    trace.setup.alpha2Exact trace.setup.alpha3Exact trace.setup.represented
    (stateCanonical.1 8) (by simpa [prepared] using blockRun8)
  have blockSem9 := foldZeroBlock_corresponds prepared alpha trace.alpha2
    trace.alpha3 state.blocks.val[9]! trace.block9 alphaCanonical
    trace.setup.alpha2Canonical trace.setup.alpha3Canonical
    trace.setup.alpha2Exact trace.setup.alpha3Exact trace.setup.represented
    (stateCanonical.1 9) (by simpa [prepared] using blockRun9)
  have deltaFactorExact : trace.deltaFactor = aspis_core.field.QM31.ONE := by
    have factorRun := trace.deltaFactorRun
    rw [foldExact] at factorRun
    exact (Result.ok.inj factorRun).symm
  have deltaFactorCanonical : Canonical trace.deltaFactor := by
    rw [deltaFactorExact]
    exact one_canonical
  have deltaHalfSem := half_run_exact trace.deltaFactor trace.deltaHalf
    deltaFactorCanonical trace.deltaHalfRun
  have deltaQuarterSem := half_run_exact trace.deltaHalf trace.deltaQuarter
    deltaHalfSem.1 trace.deltaQuarterRun
  have deltaScaleSem := mul_run_exact state.delta_scale trace.deltaQuarter
    trace.deltaScale stateCanonical.2 deltaQuarterSem.1 trace.deltaScaleRun
  have deltaQuarterExact : toK trace.deltaQuarter = toK trace.deltaFactor / 4 := by
    rw [deltaQuarterSem.2, deltaHalfSem.2, div_two_div_two]
  let target := AspisV5CompactTerminalOptimized.optimizedFoldZero
    (toK alpha) (projectState state)
  have blockCanonical : ∀ index : Fin 10,
      CanonicalBlock (traceBlock trace index) := by
    intro index
    fin_cases index
    · simpa [traceBlock, traceBlocks, Array.make] using blockSem0.1
    · simpa [traceBlock, traceBlocks, Array.make] using blockSem1.1
    · simpa [traceBlock, traceBlocks, Array.make] using blockSem2.1
    · simpa [traceBlock, traceBlocks, Array.make] using blockSem3.1
    · simpa [traceBlock, traceBlocks, Array.make] using blockSem4.1
    · simpa [traceBlock, traceBlocks, Array.make] using blockSem5.1
    · simpa [traceBlock, traceBlocks, Array.make] using blockSem6.1
    · simpa [traceBlock, traceBlocks, Array.make] using blockSem7.1
    · simpa [traceBlock, traceBlocks, Array.make] using blockSem8.1
    · simpa [traceBlock, traceBlocks, Array.make] using blockSem9.1
  have blockExact : ∀ index : Fin 10,
      projectBlock (traceBlock trace index) = target.blocks index := by
    intro index
    fin_cases index
    · simpa [traceBlock, traceBlocks, target, projectState, Array.make,
        AspisV5CompactTerminalOptimized.optimizedFoldZero,
        optimizedZeroBlock] using blockSem0.2
    · simpa [traceBlock, traceBlocks, target, projectState, Array.make,
        AspisV5CompactTerminalOptimized.optimizedFoldZero,
        optimizedZeroBlock] using blockSem1.2
    · simpa [traceBlock, traceBlocks, target, projectState, Array.make,
        AspisV5CompactTerminalOptimized.optimizedFoldZero,
        optimizedZeroBlock] using blockSem2.2
    · simpa [traceBlock, traceBlocks, target, projectState, Array.make,
        AspisV5CompactTerminalOptimized.optimizedFoldZero,
        optimizedZeroBlock] using blockSem3.2
    · simpa [traceBlock, traceBlocks, target, projectState, Array.make,
        AspisV5CompactTerminalOptimized.optimizedFoldZero,
        optimizedZeroBlock] using blockSem4.2
    · simpa [traceBlock, traceBlocks, target, projectState, Array.make,
        AspisV5CompactTerminalOptimized.optimizedFoldZero,
        optimizedZeroBlock] using blockSem5.2
    · simpa [traceBlock, traceBlocks, target, projectState, Array.make,
        AspisV5CompactTerminalOptimized.optimizedFoldZero,
        optimizedZeroBlock] using blockSem6.2
    · simpa [traceBlock, traceBlocks, target, projectState, Array.make,
        AspisV5CompactTerminalOptimized.optimizedFoldZero,
        optimizedZeroBlock] using blockSem7.2
    · simpa [traceBlock, traceBlocks, target, projectState, Array.make,
        AspisV5CompactTerminalOptimized.optimizedFoldZero,
        optimizedZeroBlock] using blockSem8.2
    · simpa [traceBlock, traceBlocks, target, projectState, Array.make,
        AspisV5CompactTerminalOptimized.optimizedFoldZero,
        optimizedZeroBlock] using blockSem9.2
  have deltaExact : toK trace.deltaScale = target.deltaScale := by
    simp only [target, AspisV5CompactTerminalOptimized.optimizedFoldZero,
      projectState]
    rw [deltaScaleSem.2, deltaQuarterExact, deltaFactorExact, one_exact]
  have assembled := trace_output_corresponds trace target blockCanonical
    blockExact deltaScaleSem.1 deltaExact
  have targetSelectors : ∀ index : Fin 10,
      (target.blocks index).selector = AspisV5CompactTerminal.blockSelector index := by
    intro index
    simpa [target, AspisV5CompactTerminalOptimized.optimizedFoldZero,
      projectState, projectBlock] using selectors index
  refine ⟨assembled.1,
    releasedSelectors_of_projection target assembled.2 targetSelectors, ?_,
    assembled.2⟩
  rw [trace.outputExact]
  change (Std.U8.wrapping_add state.folds 1#u8).val = 1
  rw [foldExact]
  rfl

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
theorem unrolled_fold_one_corresponds
    (state : State) (alpha : Raw) (output : State)
    (stateCanonical : CanonicalState state)
    (selectors : ReleasedSelectors state)
    (alphaCanonical : Canonical alpha)
    (foldExact : state.folds = foldCounterOne)
    (run : V5CompactFoldSource.unrolledFold state alpha = ok output) :
    CanonicalState output ∧ ReleasedSelectors output ∧
      output.folds.val = 2 ∧
      projectState output =
        AspisV5CompactTerminalOptimized.optimizedFoldOne
          (toK alpha) (projectState state) := by
  obtain ⟨trace⟩ := accepted_unrolled_fold_trace state alpha output
    alphaCanonical run
  let prepared := Array.make 3#usize
    [trace.prepared0, trace.prepared1, trace.prepared2]
  have blockSem (index : Fin 10) :
      CanonicalBlock (traceBlock trace index) ∧
      projectBlock (traceBlock trace index) =
        optimizedOneBlock (toK alpha)
          (projectBlock state.blocks.val[index.val]!) := by
    have blockRun := trace_block_run trace index
    rw [foldExact] at blockRun
    rw [foldBlock_one_exact] at blockRun
    exact foldOneBlock_corresponds prepared alpha trace.alpha2 trace.alpha3
      state.blocks.val[index.val]! (traceBlock trace index) alphaCanonical
      trace.setup.alpha2Canonical trace.setup.alpha3Canonical
      trace.setup.alpha2Exact trace.setup.alpha3Exact trace.setup.represented
      (stateCanonical.1 index) (by simpa [prepared] using blockRun)
  have deltaFactorExact : trace.deltaFactor = aspis_core.field.QM31.ONE := by
    have factorRun := trace.deltaFactorRun
    rw [foldExact] at factorRun
    exact (Result.ok.inj factorRun).symm
  have deltaFactorCanonical : Canonical trace.deltaFactor := by
    rw [deltaFactorExact]
    exact one_canonical
  have deltaHalfSem := half_run_exact trace.deltaFactor trace.deltaHalf
    deltaFactorCanonical trace.deltaHalfRun
  have deltaQuarterSem := half_run_exact trace.deltaHalf trace.deltaQuarter
    deltaHalfSem.1 trace.deltaQuarterRun
  have deltaScaleSem := mul_run_exact state.delta_scale trace.deltaQuarter
    trace.deltaScale stateCanonical.2 deltaQuarterSem.1 trace.deltaScaleRun
  have deltaQuarterExact : toK trace.deltaQuarter = toK trace.deltaFactor / 4 := by
    rw [deltaQuarterSem.2, deltaHalfSem.2, div_two_div_two]
  let target := AspisV5CompactTerminalOptimized.optimizedFoldOne
    (toK alpha) (projectState state)
  have blockCanonical : ∀ index : Fin 10,
      CanonicalBlock (traceBlock trace index) := fun index => (blockSem index).1
  have blockExact : ∀ index : Fin 10,
      projectBlock (traceBlock trace index) = target.blocks index := by
    intro index
    simpa [target, projectState,
      AspisV5CompactTerminalOptimized.optimizedFoldOne,
      optimizedOneBlock] using (blockSem index).2
  have deltaExact : toK trace.deltaScale = target.deltaScale := by
    simp only [target, AspisV5CompactTerminalOptimized.optimizedFoldOne,
      projectState]
    rw [deltaScaleSem.2, deltaQuarterExact, deltaFactorExact, one_exact]
  have assembled := trace_output_corresponds trace target blockCanonical
    blockExact deltaScaleSem.1 deltaExact
  have targetSelectors : ∀ index : Fin 10,
      (target.blocks index).selector = AspisV5CompactTerminal.blockSelector index := by
    intro index
    simpa [target, AspisV5CompactTerminalOptimized.optimizedFoldOne,
      projectState, projectBlock] using selectors index
  refine ⟨assembled.1,
    releasedSelectors_of_projection target assembled.2 targetSelectors, ?_,
    assembled.2⟩
  rw [trace.outputExact]
  change (Std.U8.wrapping_add state.folds 1#u8).val = 2
  rw [foldExact]
  rfl

private theorem optimizedTwoEvenBlock_eq_foldTwoBlock
    (state : State) (alpha : K) (index : Fin 10)
    (even : ((projectState state).blocks index).selector % 2 = 0) :
    optimizedTwoEvenBlock alpha
        (projectBlock state.blocks.val[index.val]!) =
      (AspisV5CompactTerminalOptimized.optimizedFoldTwo alpha
        (projectState state)).blocks index := by
  have blockExact :
      projectBlock state.blocks.val[index.val]! =
        (projectState state).blocks index := rfl
  rw [blockExact]
  simp [AspisV5CompactTerminalOptimized.optimizedFoldTwo,
    optimizedTwoEvenBlock, even]

private theorem optimizedTwoOddBlock_eq_foldTwoBlock
    (state : State) (alpha : K) (index : Fin 10)
    (odd : ((projectState state).blocks index).selector % 2 ≠ 0) :
    optimizedTwoOddBlock alpha
        (projectBlock state.blocks.val[index.val]!) =
      (AspisV5CompactTerminalOptimized.optimizedFoldTwo alpha
        (projectState state)).blocks index := by
  have blockExact :
      projectBlock state.blocks.val[index.val]! =
        (projectState state).blocks index := rfl
  rw [blockExact]
  simp [AspisV5CompactTerminalOptimized.optimizedFoldTwo,
    optimizedTwoOddBlock, odd]

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
theorem unrolled_fold_two_corresponds
    (state : State) (alpha : Raw) (output : State)
    (stateCanonical : CanonicalState state)
    (selectors : ReleasedSelectors state)
    (alphaCanonical : Canonical alpha)
    (foldExact : state.folds = foldCounterTwo)
    (run : V5CompactFoldSource.unrolledFold state alpha = ok output) :
    CanonicalState output ∧ ReleasedSelectors output ∧
      output.folds.val = 3 ∧
      projectState output =
        AspisV5CompactTerminalOptimized.optimizedFoldTwo
          (toK alpha) (projectState state) := by
  obtain ⟨trace⟩ := accepted_unrolled_fold_trace state alpha output
    alphaCanonical run
  let prepared := Array.make 3#usize
    [trace.prepared0, trace.prepared1, trace.prepared2]
  let target := AspisV5CompactTerminalOptimized.optimizedFoldTwo
    (toK alpha) (projectState state)
  have evenSem (index : Fin 10)
      (even : (state.blocks.val[index.val]!).selector &&& 1#u8 = 0#u8) :
      CanonicalBlock (traceBlock trace index) ∧
      projectBlock (traceBlock trace index) =
        optimizedTwoEvenBlock (toK alpha)
          (projectBlock state.blocks.val[index.val]!) := by
    have blockRun := trace_block_run trace index
    rw [foldExact] at blockRun
    rw [foldBlock_two_even_exact _ _ _ _ _ even] at blockRun
    exact foldTwoEvenBlock_corresponds prepared alpha trace.alpha3
      state.blocks.val[index.val]! (traceBlock trace index) alphaCanonical
      trace.setup.alpha3Canonical trace.setup.alpha3Exact
      trace.setup.represented.1 (stateCanonical.1 index)
      (by simpa [prepared] using blockRun)
  have oddSem (index : Fin 10)
      (odd : (state.blocks.val[index.val]!).selector &&& 1#u8 ≠ 0#u8) :
      CanonicalBlock (traceBlock trace index) ∧
      projectBlock (traceBlock trace index) =
        optimizedTwoOddBlock (toK alpha)
          (projectBlock state.blocks.val[index.val]!) := by
    have blockRun := trace_block_run trace index
    rw [foldExact] at blockRun
    rw [foldBlock_two_odd_exact _ _ _ _ _ odd] at blockRun
    exact foldTwoOddBlock_corresponds prepared alpha trace.alpha2
      state.blocks.val[index.val]! (traceBlock trace index) alphaCanonical
      trace.setup.alpha2Canonical trace.setup.alpha2Exact
      trace.setup.represented.2.1 trace.setup.represented.2.2
      (stateCanonical.1 index) (by simpa [prepared] using blockRun)
  have blockSem : ∀ index : Fin 10,
      CanonicalBlock (traceBlock trace index) ∧
      projectBlock (traceBlock trace index) = target.blocks index := by
    intro index
    fin_cases index
    · have selectorExact := released_selector_eq selectors (0 : Fin 10) 0#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(0 : Fin 10).val]!).selector.val = 0 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (0 : Fin 10)
      have sem := evenSem (0 : Fin 10) (by rw [selectorExact]; decide)
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedTwoEvenBlock_eq_foldTwoBlock state
        (toK alpha) (0 : Fin 10) (by
          change (state.blocks.val[(0 : Fin 10).val]!).selector.val % 2 = 0
          omega)
    · have selectorExact := released_selector_eq selectors (1 : Fin 10) 1#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(1 : Fin 10).val]!).selector.val = 1 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (1 : Fin 10)
      have sem := oddSem (1 : Fin 10) (by rw [selectorExact]; decide)
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedTwoOddBlock_eq_foldTwoBlock state
        (toK alpha) (1 : Fin 10) (by
          change (state.blocks.val[(1 : Fin 10).val]!).selector.val % 2 ≠ 0
          omega)
    · have selectorExact := released_selector_eq selectors (2 : Fin 10) 2#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(2 : Fin 10).val]!).selector.val = 2 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (2 : Fin 10)
      have sem := evenSem (2 : Fin 10) (by rw [selectorExact]; decide)
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedTwoEvenBlock_eq_foldTwoBlock state
        (toK alpha) (2 : Fin 10) (by
          change (state.blocks.val[(2 : Fin 10).val]!).selector.val % 2 = 0
          omega)
    · have selectorExact := released_selector_eq selectors (3 : Fin 10) 3#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(3 : Fin 10).val]!).selector.val = 3 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (3 : Fin 10)
      have sem := oddSem (3 : Fin 10) (by rw [selectorExact]; decide)
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedTwoOddBlock_eq_foldTwoBlock state
        (toK alpha) (3 : Fin 10) (by
          change (state.blocks.val[(3 : Fin 10).val]!).selector.val % 2 ≠ 0
          omega)
    · have selectorExact := released_selector_eq selectors (4 : Fin 10) 4#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(4 : Fin 10).val]!).selector.val = 4 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (4 : Fin 10)
      have sem := evenSem (4 : Fin 10) (by rw [selectorExact]; decide)
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedTwoEvenBlock_eq_foldTwoBlock state
        (toK alpha) (4 : Fin 10) (by
          change (state.blocks.val[(4 : Fin 10).val]!).selector.val % 2 = 0
          omega)
    · have selectorExact := released_selector_eq selectors (5 : Fin 10) 5#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(5 : Fin 10).val]!).selector.val = 5 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (5 : Fin 10)
      have sem := oddSem (5 : Fin 10) (by rw [selectorExact]; decide)
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedTwoOddBlock_eq_foldTwoBlock state
        (toK alpha) (5 : Fin 10) (by
          change (state.blocks.val[(5 : Fin 10).val]!).selector.val % 2 ≠ 0
          omega)
    · have selectorExact := released_selector_eq selectors (6 : Fin 10) 6#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(6 : Fin 10).val]!).selector.val = 6 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (6 : Fin 10)
      have sem := evenSem (6 : Fin 10) (by rw [selectorExact]; decide)
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedTwoEvenBlock_eq_foldTwoBlock state
        (toK alpha) (6 : Fin 10) (by
          change (state.blocks.val[(6 : Fin 10).val]!).selector.val % 2 = 0
          omega)
    · have selectorExact := released_selector_eq selectors (7 : Fin 10) 28#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(7 : Fin 10).val]!).selector.val = 28 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (7 : Fin 10)
      have sem := evenSem (7 : Fin 10) (by rw [selectorExact]; decide)
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedTwoEvenBlock_eq_foldTwoBlock state
        (toK alpha) (7 : Fin 10) (by
          change (state.blocks.val[(7 : Fin 10).val]!).selector.val % 2 = 0
          omega)
    · have selectorExact := released_selector_eq selectors (8 : Fin 10) 29#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(8 : Fin 10).val]!).selector.val = 29 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (8 : Fin 10)
      have sem := oddSem (8 : Fin 10) (by rw [selectorExact]; decide)
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedTwoOddBlock_eq_foldTwoBlock state
        (toK alpha) (8 : Fin 10) (by
          change (state.blocks.val[(8 : Fin 10).val]!).selector.val % 2 ≠ 0
          omega)
    · have selectorExact := released_selector_eq selectors (9 : Fin 10) 30#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(9 : Fin 10).val]!).selector.val = 30 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (9 : Fin 10)
      have sem := evenSem (9 : Fin 10) (by rw [selectorExact]; decide)
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedTwoEvenBlock_eq_foldTwoBlock state
        (toK alpha) (9 : Fin 10) (by
          change (state.blocks.val[(9 : Fin 10).val]!).selector.val % 2 = 0
          omega)
  have deltaFactorExact : trace.deltaFactor = trace.alpha2 := by
    have factorRun := trace.deltaFactorRun
    rw [foldExact] at factorRun
    exact (Result.ok.inj factorRun).symm
  have deltaFactorCanonical : Canonical trace.deltaFactor := by
    rw [deltaFactorExact]
    exact trace.setup.alpha2Canonical
  have deltaHalfSem := half_run_exact trace.deltaFactor trace.deltaHalf
    deltaFactorCanonical trace.deltaHalfRun
  have deltaQuarterSem := half_run_exact trace.deltaHalf trace.deltaQuarter
    deltaHalfSem.1 trace.deltaQuarterRun
  have deltaScaleSem := mul_run_exact state.delta_scale trace.deltaQuarter
    trace.deltaScale stateCanonical.2 deltaQuarterSem.1 trace.deltaScaleRun
  have deltaQuarterExact : toK trace.deltaQuarter = toK trace.deltaFactor / 4 := by
    rw [deltaQuarterSem.2, deltaHalfSem.2, div_two_div_two]
  have blockCanonical : ∀ index : Fin 10,
      CanonicalBlock (traceBlock trace index) := fun index => (blockSem index).1
  have blockExact : ∀ index : Fin 10,
      projectBlock (traceBlock trace index) = target.blocks index :=
    fun index => (blockSem index).2
  have deltaExact : toK trace.deltaScale = target.deltaScale := by
    simp only [target, AspisV5CompactTerminalOptimized.optimizedFoldTwo,
      projectState]
    rw [deltaScaleSem.2, deltaQuarterExact, deltaFactorExact,
      trace.setup.alpha2Exact]
  have assembled := trace_output_corresponds trace target blockCanonical
    blockExact deltaScaleSem.1 deltaExact
  have targetSelectors : ∀ index : Fin 10,
      (target.blocks index).selector = AspisV5CompactTerminal.blockSelector index := by
    intro index
    simpa [target, AspisV5CompactTerminalOptimized.optimizedFoldTwo,
      projectState, projectBlock] using selectors index
  refine ⟨assembled.1,
    releasedSelectors_of_projection target assembled.2 targetSelectors, ?_,
    assembled.2⟩
  rw [trace.outputExact]
  change (Std.U8.wrapping_add state.folds 1#u8).val = 3
  rw [foldExact]
  rfl

private theorem projected_selector_eq_of_val
    (state : State) (index : Fin 10) (value : Nat)
    (selectorVal : state.blocks.val[index.val]!.selector.val = value) :
    ((projectState state).blocks index).selector = value := by
  exact selectorVal

private theorem optimizedThreeBlock_eq_foldThreeBlock
    (state : State) (alpha factor : K) (index : Fin 10)
    (factorExact : factor =
      (if ((projectState state).blocks index).selector / 2 % 4 = 0 then 1
      else if ((projectState state).blocks index).selector / 2 % 4 = 1 then
        alpha ^ 3
      else if ((projectState state).blocks index).selector / 2 % 4 = 2 then
        alpha ^ 2
      else alpha)) :
    optimizedThreeBlock factor
        (projectBlock state.blocks.val[index.val]!) =
      (AspisV5CompactTerminalOptimized.optimizedFoldThree alpha
        (projectState state)).blocks index := by
  have blockExact :
      projectBlock state.blocks.val[index.val]! =
        (projectState state).blocks index := rfl
  rw [blockExact]
  simp [AspisV5CompactTerminalOptimized.optimizedFoldThree,
    optimizedThreeBlock, factorExact]

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
theorem unrolled_fold_three_corresponds
    (state : State) (alpha : Raw) (output : State)
    (stateCanonical : CanonicalState state)
    (selectors : ReleasedSelectors state)
    (alphaCanonical : Canonical alpha)
    (foldExact : state.folds = foldCounterThree)
    (run : V5CompactFoldSource.unrolledFold state alpha = ok output) :
    CanonicalState output ∧ ReleasedSelectors output ∧
      output.folds.val = 4 ∧
      projectState output =
        AspisV5CompactTerminalOptimized.optimizedFoldThree
          (toK alpha) (projectState state) := by
  obtain ⟨trace⟩ := accepted_unrolled_fold_trace state alpha output
    alphaCanonical run
  let target := AspisV5CompactTerminalOptimized.optimizedFoldThree
    (toK alpha) (projectState state)
  have blockRunAt (index : Fin 10) :
      V5CompactFoldSource.foldBlock foldCounterThree alpha trace.alpha2
          trace.alpha3
          (Array.make 3#usize
            [trace.prepared0, trace.prepared1, trace.prepared2])
          state.blocks.val[index.val]! = ok (traceBlock trace index) := by
    have blockRun := trace_block_run trace index
    rw [foldExact] at blockRun
    exact blockRun
  have blockSem : ∀ index : Fin 10,
      CanonicalBlock (traceBlock trace index) ∧
      projectBlock (traceBlock trace index) = target.blocks index := by
    intro index
    fin_cases index
    · have selectorExact := released_selector_eq selectors (0 : Fin 10) 0#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(0 : Fin 10).val]!).selector.val = 0 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (0 : Fin 10)
      have selected : Std.U8.wrapping_shr
          (state.blocks.val[(0 : Fin 10).val]!).selector 1#u32 &&& 3#u8 =
          (0#8#uscalar : Std.U8) := by
        rw [selectorExact]
        decide
      have blockRun := blockRunAt (0 : Fin 10)
      rw [foldBlock_three_zero_exact _ _ _ _ _ selected] at blockRun
      have sem := foldThreeBlock_corresponds aspis_core.field.QM31.ONE
        state.blocks.val[(0 : Fin 10).val]! (traceBlock trace 0) one_canonical
        (stateCanonical.1 0) blockRun
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedThreeBlock_eq_foldThreeBlock state
        (toK alpha) (toK aspis_core.field.QM31.ONE) (0 : Fin 10)
        (by
          rw [projected_selector_eq_of_val state (0 : Fin 10) 0 selectorVal]
          exact one_exact)
    · have selectorExact := released_selector_eq selectors (1 : Fin 10) 1#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(1 : Fin 10).val]!).selector.val = 1 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (1 : Fin 10)
      have selected : Std.U8.wrapping_shr
          (state.blocks.val[(1 : Fin 10).val]!).selector 1#u32 &&& 3#u8 =
          (0#8#uscalar : Std.U8) := by
        rw [selectorExact]
        decide
      have blockRun := blockRunAt (1 : Fin 10)
      rw [foldBlock_three_zero_exact _ _ _ _ _ selected] at blockRun
      have sem := foldThreeBlock_corresponds aspis_core.field.QM31.ONE
        state.blocks.val[(1 : Fin 10).val]! (traceBlock trace 1) one_canonical
        (stateCanonical.1 1) blockRun
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedThreeBlock_eq_foldThreeBlock state
        (toK alpha) (toK aspis_core.field.QM31.ONE) (1 : Fin 10)
        (by
          rw [projected_selector_eq_of_val state (1 : Fin 10) 1 selectorVal]
          exact one_exact)
    · have selectorExact := released_selector_eq selectors (2 : Fin 10) 2#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(2 : Fin 10).val]!).selector.val = 2 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (2 : Fin 10)
      have selected : Std.U8.wrapping_shr
          (state.blocks.val[(2 : Fin 10).val]!).selector 1#u32 &&& 3#u8 =
          (1#8#uscalar : Std.U8) := by
        rw [selectorExact]
        decide
      have blockRun := blockRunAt (2 : Fin 10)
      rw [foldBlock_three_one_exact _ _ _ _ _ selected] at blockRun
      have sem := foldThreeBlock_corresponds trace.alpha3
        state.blocks.val[(2 : Fin 10).val]! (traceBlock trace 2)
          trace.setup.alpha3Canonical
        (stateCanonical.1 2) blockRun
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedThreeBlock_eq_foldThreeBlock state
        (toK alpha) (toK trace.alpha3) (2 : Fin 10)
        (by
          rw [projected_selector_eq_of_val state (2 : Fin 10) 2 selectorVal]
          exact trace.setup.alpha3Exact)
    · have selectorExact := released_selector_eq selectors (3 : Fin 10) 3#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(3 : Fin 10).val]!).selector.val = 3 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (3 : Fin 10)
      have selected : Std.U8.wrapping_shr
          (state.blocks.val[(3 : Fin 10).val]!).selector 1#u32 &&& 3#u8 =
          (1#8#uscalar : Std.U8) := by
        rw [selectorExact]
        decide
      have blockRun := blockRunAt (3 : Fin 10)
      rw [foldBlock_three_one_exact _ _ _ _ _ selected] at blockRun
      have sem := foldThreeBlock_corresponds trace.alpha3
        state.blocks.val[(3 : Fin 10).val]! (traceBlock trace 3)
          trace.setup.alpha3Canonical
        (stateCanonical.1 3) blockRun
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedThreeBlock_eq_foldThreeBlock state
        (toK alpha) (toK trace.alpha3) (3 : Fin 10)
        (by
          rw [projected_selector_eq_of_val state (3 : Fin 10) 3 selectorVal]
          exact trace.setup.alpha3Exact)
    · have selectorExact := released_selector_eq selectors (4 : Fin 10) 4#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(4 : Fin 10).val]!).selector.val = 4 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (4 : Fin 10)
      have selected : Std.U8.wrapping_shr
          (state.blocks.val[(4 : Fin 10).val]!).selector 1#u32 &&& 3#u8 =
          (2#8#uscalar : Std.U8) := by
        rw [selectorExact]
        decide
      have blockRun := blockRunAt (4 : Fin 10)
      rw [foldBlock_three_two_exact _ _ _ _ _ selected] at blockRun
      have sem := foldThreeBlock_corresponds trace.alpha2
        state.blocks.val[(4 : Fin 10).val]! (traceBlock trace 4)
          trace.setup.alpha2Canonical
        (stateCanonical.1 4) blockRun
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedThreeBlock_eq_foldThreeBlock state
        (toK alpha) (toK trace.alpha2) (4 : Fin 10)
        (by
          rw [projected_selector_eq_of_val state (4 : Fin 10) 4 selectorVal]
          exact trace.setup.alpha2Exact)
    · have selectorExact := released_selector_eq selectors (5 : Fin 10) 5#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(5 : Fin 10).val]!).selector.val = 5 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (5 : Fin 10)
      have selected : Std.U8.wrapping_shr
          (state.blocks.val[(5 : Fin 10).val]!).selector 1#u32 &&& 3#u8 =
          (2#8#uscalar : Std.U8) := by
        rw [selectorExact]
        decide
      have blockRun := blockRunAt (5 : Fin 10)
      rw [foldBlock_three_two_exact _ _ _ _ _ selected] at blockRun
      have sem := foldThreeBlock_corresponds trace.alpha2
        state.blocks.val[(5 : Fin 10).val]! (traceBlock trace 5)
          trace.setup.alpha2Canonical
        (stateCanonical.1 5) blockRun
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedThreeBlock_eq_foldThreeBlock state
        (toK alpha) (toK trace.alpha2) (5 : Fin 10)
        (by
          rw [projected_selector_eq_of_val state (5 : Fin 10) 5 selectorVal]
          exact trace.setup.alpha2Exact)
    · have selectorExact := released_selector_eq selectors (6 : Fin 10) 6#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(6 : Fin 10).val]!).selector.val = 6 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (6 : Fin 10)
      have selected : Std.U8.wrapping_shr
          (state.blocks.val[(6 : Fin 10).val]!).selector 1#u32 &&& 3#u8 =
          (3#8#uscalar : Std.U8) := by
        rw [selectorExact]
        decide
      have blockRun := blockRunAt (6 : Fin 10)
      rw [foldBlock_three_three_exact _ _ _ _ _ selected] at blockRun
      have sem := foldThreeBlock_corresponds alpha
        state.blocks.val[(6 : Fin 10).val]! (traceBlock trace 6) alphaCanonical
        (stateCanonical.1 6) blockRun
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedThreeBlock_eq_foldThreeBlock state
        (toK alpha) (toK alpha) (6 : Fin 10)
        (by
          rw [projected_selector_eq_of_val state (6 : Fin 10) 6 selectorVal]
          norm_num)
    · have selectorExact := released_selector_eq selectors (7 : Fin 10) 28#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(7 : Fin 10).val]!).selector.val = 28 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (7 : Fin 10)
      have selected : Std.U8.wrapping_shr
          (state.blocks.val[(7 : Fin 10).val]!).selector 1#u32 &&& 3#u8 =
          (2#8#uscalar : Std.U8) := by
        rw [selectorExact]
        decide
      have blockRun := blockRunAt (7 : Fin 10)
      rw [foldBlock_three_two_exact _ _ _ _ _ selected] at blockRun
      have sem := foldThreeBlock_corresponds trace.alpha2
        state.blocks.val[(7 : Fin 10).val]! (traceBlock trace 7)
          trace.setup.alpha2Canonical
        (stateCanonical.1 7) blockRun
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedThreeBlock_eq_foldThreeBlock state
        (toK alpha) (toK trace.alpha2) (7 : Fin 10)
        (by
          rw [projected_selector_eq_of_val state (7 : Fin 10) 28 selectorVal]
          exact trace.setup.alpha2Exact)
    · have selectorExact := released_selector_eq selectors (8 : Fin 10) 29#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(8 : Fin 10).val]!).selector.val = 29 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (8 : Fin 10)
      have selected : Std.U8.wrapping_shr
          (state.blocks.val[(8 : Fin 10).val]!).selector 1#u32 &&& 3#u8 =
          (2#8#uscalar : Std.U8) := by
        rw [selectorExact]
        decide
      have blockRun := blockRunAt (8 : Fin 10)
      rw [foldBlock_three_two_exact _ _ _ _ _ selected] at blockRun
      have sem := foldThreeBlock_corresponds trace.alpha2
        state.blocks.val[(8 : Fin 10).val]! (traceBlock trace 8)
          trace.setup.alpha2Canonical
        (stateCanonical.1 8) blockRun
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedThreeBlock_eq_foldThreeBlock state
        (toK alpha) (toK trace.alpha2) (8 : Fin 10)
        (by
          rw [projected_selector_eq_of_val state (8 : Fin 10) 29 selectorVal]
          exact trace.setup.alpha2Exact)
    · have selectorExact := released_selector_eq selectors (9 : Fin 10) 30#u8 (by decide)
      have selectorVal :
          (state.blocks.val[(9 : Fin 10).val]!).selector.val = 30 := by
        simpa [AspisV5CompactTerminal.blockSelector] using selectors (9 : Fin 10)
      have selected : Std.U8.wrapping_shr
          (state.blocks.val[(9 : Fin 10).val]!).selector 1#u32 &&& 3#u8 =
          (3#8#uscalar : Std.U8) := by
        rw [selectorExact]
        decide
      have blockRun := blockRunAt (9 : Fin 10)
      rw [foldBlock_three_three_exact _ _ _ _ _ selected] at blockRun
      have sem := foldThreeBlock_corresponds alpha
        state.blocks.val[(9 : Fin 10).val]! (traceBlock trace 9) alphaCanonical
        (stateCanonical.1 9) blockRun
      refine ⟨sem.1, sem.2.trans ?_⟩
      simpa [target] using optimizedThreeBlock_eq_foldThreeBlock state
        (toK alpha) (toK alpha) (9 : Fin 10)
        (by
          rw [projected_selector_eq_of_val state (9 : Fin 10) 30 selectorVal]
          norm_num)
  have deltaFactorExact : trace.deltaFactor = alpha := by
    have factorRun := trace.deltaFactorRun
    rw [foldExact] at factorRun
    exact (Result.ok.inj factorRun).symm
  have deltaFactorCanonical : Canonical trace.deltaFactor := by
    rw [deltaFactorExact]
    exact alphaCanonical
  have deltaHalfSem := half_run_exact trace.deltaFactor trace.deltaHalf
    deltaFactorCanonical trace.deltaHalfRun
  have deltaQuarterSem := half_run_exact trace.deltaHalf trace.deltaQuarter
    deltaHalfSem.1 trace.deltaQuarterRun
  have deltaScaleSem := mul_run_exact state.delta_scale trace.deltaQuarter
    trace.deltaScale stateCanonical.2 deltaQuarterSem.1 trace.deltaScaleRun
  have deltaQuarterExact : toK trace.deltaQuarter = toK trace.deltaFactor / 4 := by
    rw [deltaQuarterSem.2, deltaHalfSem.2, div_two_div_two]
  have blockCanonical : ∀ index : Fin 10,
      CanonicalBlock (traceBlock trace index) := fun index => (blockSem index).1
  have blockExact : ∀ index : Fin 10,
      projectBlock (traceBlock trace index) = target.blocks index :=
    fun index => (blockSem index).2
  have deltaExact : toK trace.deltaScale = target.deltaScale := by
    simp only [target, AspisV5CompactTerminalOptimized.optimizedFoldThree,
      projectState]
    rw [deltaScaleSem.2, deltaQuarterExact, deltaFactorExact]
  have assembled := trace_output_corresponds trace target blockCanonical
    blockExact deltaScaleSem.1 deltaExact
  have targetSelectors : ∀ index : Fin 10,
      (target.blocks index).selector = AspisV5CompactTerminal.blockSelector index := by
    intro index
    simpa [target, AspisV5CompactTerminalOptimized.optimizedFoldThree,
      projectState, projectBlock] using selectors index
  refine ⟨assembled.1,
    releasedSelectors_of_projection target assembled.2 targetSelectors, ?_,
    assembled.2⟩
  rw [trace.outputExact]
  change (Std.U8.wrapping_add state.folds 1#u8).val = 4
  rw [foldExact]
  rfl

def optimizedFoldFor (folds : Nat) (alpha : K)
    (state : AspisV5CompactTerminalOptimized.OptimizedState K) :
    AspisV5CompactTerminalOptimized.OptimizedState K :=
  match folds with
  | 0 => AspisV5CompactTerminalOptimized.optimizedFoldZero alpha state
  | 1 => AspisV5CompactTerminalOptimized.optimizedFoldOne alpha state
  | 2 => AspisV5CompactTerminalOptimized.optimizedFoldTwo alpha state
  | 3 => AspisV5CompactTerminalOptimized.optimizedFoldThree alpha state
  | _ => state

/-- Exact maintained-field meaning of the explicit ten-block program shared
by the corrected wrapper and the exact Aeneas extraction. -/
theorem unrolled_fold_corresponds
    (state : State) (alpha : Raw) (output : State)
    (stateCanonical : CanonicalState state)
    (selectors : ReleasedSelectors state)
    (alphaCanonical : Canonical alpha)
    (foldBound : state.folds.val < 4)
    (run : V5CompactFoldSource.unrolledFold state alpha = ok output) :
    CanonicalState output ∧ ReleasedSelectors output ∧
      output.folds.val = state.folds.val + 1 ∧
      projectState output =
        optimizedFoldFor state.folds.val (toK alpha) (projectState state) := by
  have foldCases : state.folds.val = 0 ∨ state.folds.val = 1 ∨
      state.folds.val = 2 ∨ state.folds.val = 3 := by
    omega
  rcases foldCases with foldValue | foldValue | foldValue | foldValue
  · have foldExact : state.folds = foldCounterZero := by
      apply UScalar.eq_of_val_eq
      change state.folds.val = 0
      exact foldValue
    have semantic := unrolled_fold_zero_corresponds state alpha output
      stateCanonical selectors alphaCanonical foldExact run
    refine ⟨semantic.1, semantic.2.1, ?_, ?_⟩
    · rw [semantic.2.2.1, foldValue]
    · rw [foldValue]
      exact semantic.2.2.2
  · have foldExact : state.folds = foldCounterOne := by
      apply UScalar.eq_of_val_eq
      change state.folds.val = 1
      exact foldValue
    have semantic := unrolled_fold_one_corresponds state alpha output
      stateCanonical selectors alphaCanonical foldExact run
    refine ⟨semantic.1, semantic.2.1, ?_, ?_⟩
    · rw [semantic.2.2.1, foldValue]
    · rw [foldValue]
      exact semantic.2.2.2
  · have foldExact : state.folds = foldCounterTwo := by
      apply UScalar.eq_of_val_eq
      change state.folds.val = 2
      exact foldValue
    have semantic := unrolled_fold_two_corresponds state alpha output
      stateCanonical selectors alphaCanonical foldExact run
    refine ⟨semantic.1, semantic.2.1, ?_, ?_⟩
    · rw [semantic.2.2.1, foldValue]
    · rw [foldValue]
      exact semantic.2.2.2
  · have foldExact : state.folds = foldCounterThree := by
      apply UScalar.eq_of_val_eq
      change state.folds.val = 3
      exact foldValue
    have semantic := unrolled_fold_three_corresponds state alpha output
      stateCanonical selectors alphaCanonical foldExact run
    refine ⟨semantic.1, semantic.2.1, ?_, ?_⟩
    · rw [semantic.2.2.1, foldValue]
    · rw [foldValue]
      exact semantic.2.2.2

/-- Exact maintained-field meaning of every successful corrected compact-fold
call in the released four-fold schedule.  The corrected wrapper differs from
the preserved raw Aeneas artifact only at the mutable iterator hand-back that
the raw outer wrapper assembled against an empty iterator. -/
theorem corrected_fold_corresponds
    (state : State) (alpha : Raw) (output : State)
    (stateCanonical : CanonicalState state)
    (selectors : ReleasedSelectors state)
    (alphaCanonical : Canonical alpha)
    (foldBound : state.folds.val < 4)
    (run : V5CompactFoldCorrectedWrapper.fold state alpha = ok output) :
    CanonicalState output ∧ ReleasedSelectors output ∧
      output.folds.val = state.folds.val + 1 ∧
      projectState output =
        optimizedFoldFor state.folds.val (toK alpha) (projectState state) := by
  apply unrolled_fold_corresponds state alpha output stateCanonical selectors
    alphaCanonical foldBound
  exact V5CompactFoldSource.fold_success_unrolled state output alpha foldBound run

#print axioms prepared_setup_exists
#print axioms accepted_unrolled_fold_trace
#print axioms trace_output_corresponds
#print axioms unrolled_fold_zero_corresponds
#print axioms unrolled_fold_one_corresponds
#print axioms unrolled_fold_two_corresponds
#print axioms unrolled_fold_three_corresponds
#print axioms unrolled_fold_corresponds
#print axioms corrected_fold_corresponds

end AspisV5CompactFoldProgramSemantics
