import V5RelationCompactFoldGenerated

/-!
# Extracted compact relation-fold block transitions

Pinned Aeneas emits the complete body of the ten-block loop in production
`CompactBTerminalWeights::fold`, but its mutable-iterator back-function makes
the enclosing loop wrapper ill typed.  This file removes ambiguity from the
body that was emitted.  For every possible block and field values, it proves
the exact update performed at fold counters zero through three, including
both selector-bit branches in fold two and all four selector-pair branches in
fold three.

The premises name only the standard mutable-iterator `next` result emitted by
Aeneas.  They do not assume any field equation or replace a Rust call by a
fixture.  The conclusions retain every generated multiplication, prepared
sum, halving, squaring, and block write in source order.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5RelationCompactFoldKernelProof

open V5RelationCompactFoldGenerated

abbrev RawQM31 := V5RelationCompactFoldGenerated.aspis_core.field.QM31
abbrev Prepared :=
  V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier
abbrev Block :=
  V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev Iter := core.slice.iter.IterMut Block
abbrev Back := Iter → Iter
abbrev NextBack := Iter → Option Block → Iter
abbrev FoldFlow := ControlFlow (Iter × Back × Std.U8) (Std.U8 × Back)

/-- Install one successfully transformed block back into the generated
mutable-iterator continuation. -/
def continueWith
    (iter : Iter) (nextBack : NextBack) (back : Back) (counter : Std.U8)
    (blockResult : Result Block) : Result FoldFlow := do
  let updated ← blockResult
  ok (cont (iter, fun output ↦ back (nextBack output (some updated)), counter))

/-- Exact block update at `self.folds = 0`. -/
def foldZeroBlock
    (preparedPowers : Array Prepared 3#usize) (block : Block) : Result Block := do
  let highTimesLow ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
      block.power_hi block.power_lo
  let weighted ←
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared
      preparedPowers
      (Array.make 3#usize [block.power_lo, block.power_hi, highTimesLow])
  let factor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.add
      V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE weighted
  let powerLo ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.square block.power_hi
  let powerHi ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.square powerLo
  let halfFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half factor
  let quarterFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half halfFactor
  let scale ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
      block.scale quarterFactor
  ok { block with scale, power_lo := powerLo, power_hi := powerHi }

/-- Exact block update at `self.folds = 1`. -/
def foldOneBlock
    (preparedPowers : Array Prepared 3#usize) (block : Block) : Result Block := do
  let highTimesLow ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
      block.power_hi block.power_lo
  let lowerWeighted ←
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared
      preparedPowers
      (Array.make 3#usize [block.power_lo, block.power_hi, highTimesLow])
  let lower ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.add
      V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE lowerWeighted
  let lowerHalf ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half lower
  let lowerQuarter ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half lowerHalf
  let highSquared ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.square block.power_hi
  let prepared0 ← Array.index_usize preparedPowers 0#usize
  let prepared1 ← Array.index_usize preparedPowers 1#usize
  let upperWeighted ←
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared
      (Array.make 2#usize [prepared0, prepared1])
      (Array.make 2#usize [block.power_lo, block.power_hi])
  let upper ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.add
      V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE upperWeighted
  let upperProduct ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul highSquared upper
  let upperHalf ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half upperProduct
  let upperQuarter ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half upperHalf
  let scale ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
      block.scale lowerQuarter
  let powerLo ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
      block.scale upperQuarter
  ok {
    block with
      scale, power_lo := powerLo,
      power_hi := V5RelationCompactFoldGenerated.aspis_core.field.QM31.ZERO
  }

/-- Exact even-selector block update at `self.folds = 2`. -/
def foldTwoEvenBlock
    (preparedPowers : Array Prepared 3#usize) (block : Block) : Result Block := do
  let prepared0 ← Array.index_usize preparedPowers 0#usize
  let weighted ←
    V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier.mul
      prepared0 block.power_lo
  let factor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.add block.scale weighted
  let halfFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half factor
  let quarterFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half halfFactor
  ok {
    block with
      scale := quarterFactor,
      power_lo := V5RelationCompactFoldGenerated.aspis_core.field.QM31.ZERO
  }

/-- Exact odd-selector block update at `self.folds = 2`. -/
def foldTwoOddBlock
    (preparedPowers : Array Prepared 3#usize) (block : Block) : Result Block := do
  let prepared1 ← Array.index_usize preparedPowers 1#usize
  let prepared2 ← Array.index_usize preparedPowers 2#usize
  let factor ←
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared
      (Array.make 2#usize [prepared1, prepared2])
      (Array.make 2#usize [block.scale, block.power_lo])
  let halfFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half factor
  let quarterFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half halfFactor
  ok {
    block with
      scale := quarterFactor,
      power_lo := V5RelationCompactFoldGenerated.aspis_core.field.QM31.ZERO
  }

/-- Exact block update at `self.folds = 3`, once the selector-pair multiplier
has been chosen. -/
def foldThreeBlock (factor : RawQM31) (block : Block) : Result Block := do
  let halfFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half factor
  let quarterFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half halfFactor
  let scale ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
      block.scale quarterFactor
  ok { block with scale }

/-! The next four programs include the iterator write-back.  They are kept
separate from the block-only definitions above because `Result.bind` is not
definitionally associative: a direct source equality should not depend on a
separate monad-law rewrite. -/

def foldZeroStep
    (preparedPowers : Array Prepared 3#usize) (block : Block)
    (iterAfter : Iter) (nextBack : NextBack) (back : Back) : Result FoldFlow := do
  let highTimesLow ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
      block.power_hi block.power_lo
  let weighted ←
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared
      preparedPowers
      (Array.make 3#usize [block.power_lo, block.power_hi, highTimesLow])
  let factor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.add
      V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE weighted
  let powerLo ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.square block.power_hi
  let powerHi ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.square powerLo
  let halfFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half factor
  let quarterFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half halfFactor
  let scale ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
      block.scale quarterFactor
  ok (cont (iterAfter,
    fun output ↦ back (nextBack output (some
      { block with scale, power_lo := powerLo, power_hi := powerHi })),
    0#u8))

def foldOneStep
    (preparedPowers : Array Prepared 3#usize) (block : Block)
    (iterAfter : Iter) (nextBack : NextBack) (back : Back) : Result FoldFlow := do
  let highTimesLow ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
      block.power_hi block.power_lo
  let lowerWeighted ←
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared
      preparedPowers
      (Array.make 3#usize [block.power_lo, block.power_hi, highTimesLow])
  let lower ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.add
      V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE lowerWeighted
  let lowerHalf ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half lower
  let lowerQuarter ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half lowerHalf
  let highSquared ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.square block.power_hi
  let prepared0 ← Array.index_usize preparedPowers 0#usize
  let prepared1 ← Array.index_usize preparedPowers 1#usize
  let upperWeighted ←
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared
      (Array.make 2#usize [prepared0, prepared1])
      (Array.make 2#usize [block.power_lo, block.power_hi])
  let upper ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.add
      V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE upperWeighted
  let upperProduct ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul highSquared upper
  let upperHalf ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half upperProduct
  let upperQuarter ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half upperHalf
  let scale ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
      block.scale lowerQuarter
  let powerLo ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
      block.scale upperQuarter
  ok (cont (iterAfter,
    fun output ↦ back (nextBack output (some
      {
        block with
          scale, power_lo := powerLo,
          power_hi := V5RelationCompactFoldGenerated.aspis_core.field.QM31.ZERO
      })),
    1#u8))

def foldTwoEvenStep
    (preparedPowers : Array Prepared 3#usize) (block : Block)
    (iterAfter : Iter) (nextBack : NextBack) (back : Back) : Result FoldFlow := do
  let prepared0 ← Array.index_usize preparedPowers 0#usize
  let weighted ←
    V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier.mul
      prepared0 block.power_lo
  let factor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.add block.scale weighted
  let halfFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half factor
  let quarterFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half halfFactor
  ok (cont (iterAfter,
    fun output ↦ back (nextBack output (some
      {
        block with
          scale := quarterFactor,
          power_lo := V5RelationCompactFoldGenerated.aspis_core.field.QM31.ZERO
      })),
    2#u8))

def foldTwoOddStep
    (preparedPowers : Array Prepared 3#usize) (block : Block)
    (iterAfter : Iter) (nextBack : NextBack) (back : Back) : Result FoldFlow := do
  let prepared1 ← Array.index_usize preparedPowers 1#usize
  let prepared2 ← Array.index_usize preparedPowers 2#usize
  let factor ←
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products2_prepared
      (Array.make 2#usize [prepared1, prepared2])
      (Array.make 2#usize [block.scale, block.power_lo])
  let halfFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half factor
  let quarterFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half halfFactor
  ok (cont (iterAfter,
    fun output ↦ back (nextBack output (some
      {
        block with
          scale := quarterFactor,
          power_lo := V5RelationCompactFoldGenerated.aspis_core.field.QM31.ZERO
      })),
    2#u8))

def foldThreeStep
    (factor : RawQM31) (block : Block)
    (iterAfter : Iter) (nextBack : NextBack) (back : Back) : Result FoldFlow := do
  let halfFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half factor
  let quarterFactor ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half halfFactor
  let scale ←
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
      block.scale quarterFactor
  ok (cont (iterAfter,
    fun output ↦ back (nextBack output (some { block with scale })),
    3#u8))

/-- The direct fold-zero step is the block transformation followed by the
generated iterator write-back. -/
theorem foldZeroStep_eq_continueWith
    (preparedPowers : Array Prepared 3#usize) (block : Block)
    (iterAfter : Iter) (nextBack : NextBack) (back : Back) :
    foldZeroStep preparedPowers block iterAfter nextBack back =
      continueWith iterAfter nextBack back 0#u8
        (foldZeroBlock preparedPowers block) := by
  simp [foldZeroStep, continueWith, foldZeroBlock]

/-- The direct fold-one step is the block transformation followed by the
generated iterator write-back. -/
theorem foldOneStep_eq_continueWith
    (preparedPowers : Array Prepared 3#usize) (block : Block)
    (iterAfter : Iter) (nextBack : NextBack) (back : Back) :
    foldOneStep preparedPowers block iterAfter nextBack back =
      continueWith iterAfter nextBack back 1#u8
        (foldOneBlock preparedPowers block) := by
  simp [foldOneStep, continueWith, foldOneBlock]

/-- The direct even-selector fold-two step is the block transformation
followed by the generated iterator write-back. -/
theorem foldTwoEvenStep_eq_continueWith
    (preparedPowers : Array Prepared 3#usize) (block : Block)
    (iterAfter : Iter) (nextBack : NextBack) (back : Back) :
    foldTwoEvenStep preparedPowers block iterAfter nextBack back =
      continueWith iterAfter nextBack back 2#u8
        (foldTwoEvenBlock preparedPowers block) := by
  simp [foldTwoEvenStep, continueWith, foldTwoEvenBlock]

/-- The direct odd-selector fold-two step is the block transformation
followed by the generated iterator write-back. -/
theorem foldTwoOddStep_eq_continueWith
    (preparedPowers : Array Prepared 3#usize) (block : Block)
    (iterAfter : Iter) (nextBack : NextBack) (back : Back) :
    foldTwoOddStep preparedPowers block iterAfter nextBack back =
      continueWith iterAfter nextBack back 2#u8
        (foldTwoOddBlock preparedPowers block) := by
  simp [foldTwoOddStep, continueWith, foldTwoOddBlock]

/-- The direct fold-three step is the chosen-factor block transformation
followed by the generated iterator write-back. -/
theorem foldThreeStep_eq_continueWith
    (factor : RawQM31) (block : Block)
    (iterAfter : Iter) (nextBack : NextBack) (back : Back) :
    foldThreeStep factor block iterAfter nextBack back =
      continueWith iterAfter nextBack back 3#u8
        (foldThreeBlock factor block) := by
  simp [foldThreeStep, continueWith, foldThreeBlock]

/-- Fold zero performs exactly the production degree-low block update and
keeps the fold counter at zero for the next block. -/
theorem extracted_fold_zero_block_exact
    (alpha alpha2 alpha3 : RawQM31)
    (preparedPowers : Array Prepared 3#usize)
    (iter iterAfter : Iter) (nextBack : NextBack) (back : Back) (block : Block)
    (nextRun :
      core.slice.iter.IteratorIterMut.next iter =
        .ok (some block, iterAfter, nextBack)) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back 0#u8 =
      foldZeroStep preparedPowers block iterAfter nextBack back := by
  change
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back
          (@UScalar.mk .U8 (0#8)) =
      foldZeroStep preparedPowers block iterAfter nextBack back
  unfold
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
  simp only [nextRun, bind_tc_ok]
  unfold foldZeroStep
  simp only [if_neg (by decide : (0#u8 : Std.U8) ≠ 2#u8)]

/-- Fold one performs exactly the lower/upper truncated-degree update and
keeps the fold counter at one for the next block. -/
theorem extracted_fold_one_block_exact
    (alpha alpha2 alpha3 : RawQM31)
    (preparedPowers : Array Prepared 3#usize)
    (iter iterAfter : Iter) (nextBack : NextBack) (back : Back) (block : Block)
    (nextRun :
      core.slice.iter.IteratorIterMut.next iter =
        .ok (some block, iterAfter, nextBack)) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back 1#u8 =
      foldOneStep preparedPowers block iterAfter nextBack back := by
  change
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back
          (@UScalar.mk .U8 (1#8)) =
      foldOneStep preparedPowers block iterAfter nextBack back
  unfold
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
  simp only [nextRun, bind_tc_ok]
  unfold foldOneStep
  rfl

/-- Fold two's even-selector branch is exact. -/
theorem extracted_fold_two_even_block_exact
    (alpha alpha2 alpha3 : RawQM31)
    (preparedPowers : Array Prepared 3#usize)
    (iter iterAfter : Iter) (nextBack : NextBack) (back : Back) (block : Block)
    (nextRun :
      core.slice.iter.IteratorIterMut.next iter =
        .ok (some block, iterAfter, nextBack))
    (even : (block.selector &&& 1#u8) = 0#u8) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back 2#u8 =
      foldTwoEvenStep preparedPowers block iterAfter nextBack back := by
  change
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back
          (@UScalar.mk .U8 (2#8)) =
      foldTwoEvenStep preparedPowers block iterAfter nextBack back
  unfold
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
  simp only [nextRun, Aeneas.Std.lift, bind_tc_ok]
  have evenExplicit :
      (block.selector &&& 1#u8) = @UScalar.mk .U8 (0#8) := even
  rw [evenExplicit]
  unfold foldTwoEvenStep
  rfl

/-- Fold two's odd-selector branch is exact. -/
theorem extracted_fold_two_odd_block_exact
    (alpha alpha2 alpha3 : RawQM31)
    (preparedPowers : Array Prepared 3#usize)
    (iter iterAfter : Iter) (nextBack : NextBack) (back : Back) (block : Block)
    (nextRun :
      core.slice.iter.IteratorIterMut.next iter =
        .ok (some block, iterAfter, nextBack))
    (odd : (block.selector &&& 1#u8) ≠ 0#u8) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back 2#u8 =
      foldTwoOddStep preparedPowers block iterAfter nextBack back := by
  change
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back
          (@UScalar.mk .U8 (2#8)) =
      foldTwoOddStep preparedPowers block iterAfter nextBack back
  unfold
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
  simp only [nextRun, Aeneas.Std.lift, bind_tc_ok]
  rw [if_neg odd]
  unfold foldTwoOddStep
  rfl

/-- Fold three uses multiplier one when selector bits one and two are zero. -/
theorem extracted_fold_three_pair_zero_exact
    (alpha alpha2 alpha3 : RawQM31)
    (preparedPowers : Array Prepared 3#usize)
    (iter iterAfter : Iter) (nextBack : NextBack) (back : Back) (block : Block)
    (nextRun :
      core.slice.iter.IteratorIterMut.next iter =
        .ok (some block, iterAfter, nextBack))
    (selectorPair :
      (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) = 0#u8) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back 3#u8 =
      foldThreeStep
        V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE block
          iterAfter nextBack back := by
  change
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back
          (@UScalar.mk .U8 (3#8)) =
      foldThreeStep
        V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE block
          iterAfter nextBack back
  unfold
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
  simp only [nextRun, Aeneas.Std.lift, bind_tc_ok]
  have selectorPairExplicit :
      (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) =
        @UScalar.mk .U8 (0#8) := selectorPair
  rw [selectorPairExplicit]
  unfold foldThreeStep
  rfl

/-- Fold three uses `alpha^3`'s prepared value when selector bits are one. -/
theorem extracted_fold_three_pair_one_exact
    (alpha alpha2 alpha3 : RawQM31)
    (preparedPowers : Array Prepared 3#usize)
    (iter iterAfter : Iter) (nextBack : NextBack) (back : Back) (block : Block)
    (nextRun :
      core.slice.iter.IteratorIterMut.next iter =
        .ok (some block, iterAfter, nextBack))
    (selectorPair :
      (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) = 1#u8) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back 3#u8 =
      foldThreeStep alpha3 block iterAfter nextBack back := by
  change
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back
          (@UScalar.mk .U8 (3#8)) =
      foldThreeStep alpha3 block iterAfter nextBack back
  unfold
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
  simp only [nextRun, Aeneas.Std.lift, bind_tc_ok]
  have selectorPairExplicit :
      (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) =
        @UScalar.mk .U8 (1#8) := selectorPair
  rw [selectorPairExplicit]
  unfold foldThreeStep
  rfl

/-- Fold three uses `alpha^2`'s prepared value when selector bits are two. -/
theorem extracted_fold_three_pair_two_exact
    (alpha alpha2 alpha3 : RawQM31)
    (preparedPowers : Array Prepared 3#usize)
    (iter iterAfter : Iter) (nextBack : NextBack) (back : Back) (block : Block)
    (nextRun :
      core.slice.iter.IteratorIterMut.next iter =
        .ok (some block, iterAfter, nextBack))
    (selectorPair :
      (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) = 2#u8) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back 3#u8 =
      foldThreeStep alpha2 block iterAfter nextBack back := by
  change
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back
          (@UScalar.mk .U8 (3#8)) =
      foldThreeStep alpha2 block iterAfter nextBack back
  unfold
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
  simp only [nextRun, Aeneas.Std.lift, bind_tc_ok]
  have selectorPairExplicit :
      (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) =
        @UScalar.mk .U8 (2#8) := selectorPair
  rw [selectorPairExplicit]
  unfold foldThreeStep
  rfl

/-- Fold three uses `alpha` when selector bits are three. -/
theorem extracted_fold_three_pair_three_exact
    (alpha alpha2 alpha3 : RawQM31)
    (preparedPowers : Array Prepared 3#usize)
    (iter iterAfter : Iter) (nextBack : NextBack) (back : Back) (block : Block)
    (nextRun :
      core.slice.iter.IteratorIterMut.next iter =
        .ok (some block, iterAfter, nextBack))
    (selectorPair :
      (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) = 3#u8) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back 3#u8 =
      foldThreeStep alpha block iterAfter nextBack back := by
  change
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back
          (@UScalar.mk .U8 (3#8)) =
      foldThreeStep alpha block iterAfter nextBack back
  unfold
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
  simp only [nextRun, Aeneas.Std.lift, bind_tc_ok]
  have selectorPairExplicit :
      (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) =
        @UScalar.mk .U8 (3#8) := selectorPair
  rw [selectorPairExplicit]
  unfold foldThreeStep
  rfl

/-- Iterator exhaustion performs no arithmetic or block update and returns
the current fold counter unchanged. -/
theorem extracted_fold_body_iterator_done
    (alpha alpha2 alpha3 : RawQM31)
    (preparedPowers : Array Prepared 3#usize)
    (iter iterAfter : Iter) (nextBack : NextBack) (back : Back)
    (counter : Std.U8)
    (nextRun :
      core.slice.iter.IteratorIterMut.next iter =
        .ok (none, iterAfter, nextBack)) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 preparedPowers iter back counter =
      .ok (done (counter,
        fun output ↦ back (nextBack output none))) := by
  unfold
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
  simp [nextRun]

#print axioms extracted_fold_zero_block_exact
#print axioms extracted_fold_one_block_exact
#print axioms extracted_fold_two_even_block_exact
#print axioms extracted_fold_two_odd_block_exact
#print axioms extracted_fold_three_pair_zero_exact
#print axioms extracted_fold_three_pair_one_exact
#print axioms extracted_fold_three_pair_two_exact
#print axioms extracted_fold_three_pair_three_exact
#print axioms extracted_fold_body_iterator_done
#print axioms foldZeroStep_eq_continueWith
#print axioms foldOneStep_eq_continueWith
#print axioms foldTwoEvenStep_eq_continueWith
#print axioms foldTwoOddStep_eq_continueWith
#print axioms foldThreeStep_eq_continueWith

end AspisV5RelationCompactFoldKernelProof
