import GoodMatricesCurrent.SourceExtractedGoodAMatrixOutput
import GoodMatricesCurrent.RuntimeKernelConcreteBridge

open Matrix Polynomial

namespace GoodMatricesCurrent.ConcreteProbeTerminalMatrixDischarge

open AspisCircleRectangularMasking
open AspisCircleTensorBinding
open AspisV5AtomicComponentACorrespondence
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentADeployedTerminalApplicability.ConcreteProbeWitness
open AspisV5ComponentATerminalRankPredicate
open AspisV5FreezeAScheduleAvailability
open AspisV5GoodGateSparseShift
open GoodMatricesCurrent.ProbeAbstractDot
open GoodMatricesCurrent.ProbeGeneratedConcrete
open GoodMatricesCurrent.ProbeTerminalMatrix
open GoodMatricesCurrent.ProbeTerminalMatrixAssembly
open GoodMatricesCurrent.RuntimeKernelConcreteBridge
open GoodMatricesCurrent.SourceExtractedGoodAMatrixOutput
open GoodMatricesCurrent.SourceExtractedGoodAModelBridge
open GoodMatricesCurrent.SourceExtractedTerminalEvaluator
open GoodMatricesCurrent.SourceExtractedTerminalWeights

abbrev Base := AspisV5ComponentADeployedTerminalApplicability.Base
abbrev Tower := AspisV5ComponentADeployedTerminalApplicability.Tower
abbrev Source := AspisV5ComponentADeployedTerminalApplicability.Source
abbrev TowerSource := AspisV5ComponentADeployedTerminalApplicability.TowerSource

private def layoutRowFin (index : Fin originalWidth) : Fin traceRows :=
  ⟨layoutRow index, by
    have h := (layoutRow_mem_reserved index).2
    norm_num [reservedStart, maskB, traceRows] at h ⊢
    omega⟩

private theorem alignedReserveEmbed_apply
    {K : Type*} [Field K] (values : Fin originalWidth → K)
    (row : Fin traceRows) :
    alignedReserveEmbed K values row =
      ∑ index : Fin originalWidth,
        if layoutRow index = (row : ℕ) then values index else 0 := by
  rfl

/-- The maintained aligned encoder contributes exactly one physical row per
natural coefficient.  This is the explicit layout/sum bridge used below. -/
theorem multilinearEvalValue_alignedReserveEmbed
    {K : Type*} [Field K] (point : TranscriptPoint K)
    (values : Fin originalWidth → K) :
    multilinearEvalValue point (alignedReserveEmbed K values) =
      ∑ index : Fin originalWidth,
        mleRowWeight point (layoutRowFin index) * values index := by
  unfold multilinearEvalValue
  simp_rw [alignedReserveEmbed_apply]
  calc
    (∑ row : Fin traceRows, mleRowWeight point row *
        ∑ index : Fin originalWidth,
          if layoutRow index = (row : ℕ) then values index else 0) =
        ∑ row : Fin traceRows, ∑ index : Fin originalWidth,
          mleRowWeight point row *
            (if layoutRow index = (row : ℕ) then values index else 0) := by
      apply Finset.sum_congr rfl
      intro row _
      exact Finset.mul_sum _ _ _
    _ = ∑ index : Fin originalWidth, ∑ row : Fin traceRows,
          mleRowWeight point row *
            (if layoutRow index = (row : ℕ) then values index else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      let target : Fin traceRows := layoutRowFin index
      rw [Finset.sum_eq_single target]
      · simp [target, layoutRowFin]
      · intro row _ hne
        have hvalues : layoutRow index ≠ (row : ℕ) := by
          intro heq
          apply hne
          apply Fin.ext
          exact heq.symm
        simp [hvalues]
      · simp

private def suffixBit (index : Fin 64) (coordinate : Fin 6) : Bool :=
  Nat.testBit index.val (5 - coordinate.val)

private def suffixWeight6 {K : Type*} [CommRing K]
    (point : TranscriptPoint K) (index : Fin 64) : K :=
  ∏ coordinate : Fin 6,
    if suffixBit index coordinate then point ⟨3 + coordinate.val, by omega⟩
    else 1 - point ⟨3 + coordinate.val, by omega⟩

private theorem suffixBit_zero (index : Fin 64) :
    suffixBit index 0 = index.val.testBit 5 := by rfl

private theorem suffixBit_one (index : Fin 64) :
    suffixBit index 1 = index.val.testBit 4 := by rfl

private theorem suffixBit_two (index : Fin 64) :
    suffixBit index 2 = index.val.testBit 3 := by rfl

private theorem suffixBit_three (index : Fin 64) :
    suffixBit index 3 = index.val.testBit 2 := by rfl

private theorem suffixBit_four (index : Fin 64) :
    suffixBit index 4 = index.val.testBit 1 := by rfl

private theorem suffixBit_five (index : Fin 64) :
    suffixBit index 5 = index.val.testBit 0 := by rfl

private def xPrefix {K : Type*} [CommRing K]
    (point : TranscriptPoint K) : K :=
  point 0 * point 1 * point 2 * (1 - point 9)

private def yPrefix {K : Type*} [CommRing K]
    (point : TranscriptPoint K) : K :=
  point 0 * point 1 * point 2 * point 9

private theorem layoutRowFin_x_val (index : Fin 48) :
    (layoutRowFin (Fin.castAdd 48 index) : ℕ) =
      2 ^ 7 * 7 + 2 * index.val := by
  simp [layoutRowFin, layoutRow, reservedStart, originalHalf]

private theorem layoutRowFin_y_val (index : Fin 48) :
    (layoutRowFin (Fin.natAdd 48 index) : ℕ) =
      2 ^ 7 * 7 + (2 * index.val + 1) := by
  simp [layoutRowFin, layoutRow, reservedStart, originalHalf]
  omega

private theorem testBit_twice_succ (value bit : Nat) :
    (2 * value).testBit (bit + 1) = value.testBit bit := by
  rw [Nat.mul_comm]
  simpa using Nat.testBit_mul_two_pow value (bit + 1) 1

private theorem testBit_twice_add_one_succ (value bit : Nat) :
    (2 * value + 1).testBit (bit + 1) = value.testBit bit := by
  rw [show 2 * value + 1 = 2 ^ 1 * value + 1 by omega]
  rw [Nat.testBit_two_pow_mul_add value (by norm_num) (bit + 1)]
  simp

private theorem prod_fin_six {K : Type*} [CommMonoid K] (f : Fin 6 → K) :
    (∏ index : Fin 6, f index) =
      f 0 * (f 1 * (f 2 * (f 3 * (f 4 * f 5)))) := by
  simp [Fin.prod_univ_succ]

private theorem prod_fin_ten {K : Type*} [CommMonoid K] (f : Fin 10 → K) :
    (∏ index : Fin 10, f index) =
      f 0 * (f 1 * (f 2 * (f 3 * (f 4 * (f 5 *
        (f 6 * (f 7 * (f 8 * f 9)))))))) := by
  simp [Fin.prod_univ_succ]

private theorem suffixWeight6_explicit {K : Type*} [CommRing K]
    (point : TranscriptPoint K) (index : Fin 64) :
    suffixWeight6 point index =
      (if index.val.testBit 5 then point 3 else 1 - point 3) *
      ((if index.val.testBit 4 then point 4 else 1 - point 4) *
      ((if index.val.testBit 3 then point 5 else 1 - point 5) *
      ((if index.val.testBit 2 then point 6 else 1 - point 6) *
      ((if index.val.testBit 1 then point 7 else 1 - point 7) *
       (if index.val.testBit 0 then point 8 else 1 - point 8))))) := by
  unfold suffixWeight6
  rw [prod_fin_six]
  rw [suffixBit_zero, suffixBit_one, suffixBit_two, suffixBit_three,
    suffixBit_four, suffixBit_five]
  simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod]
  rfl

private theorem suffixWeight6_explicit_raw {K : Type*} [CommRing K]
    (point : TranscriptPoint K) (index : Fin 64) :
    suffixWeight6 point index =
      (if index.val.testBit 5 then point ⟨3 + 0, by omega⟩
        else 1 - point ⟨3 + 0, by omega⟩) *
      ((if index.val.testBit 4 then point ⟨3 + 1, by omega⟩
        else 1 - point ⟨3 + 1, by omega⟩) *
      ((if index.val.testBit 3 then point ⟨3 + 2, by omega⟩
        else 1 - point ⟨3 + 2, by omega⟩) *
      ((if index.val.testBit 2 then point ⟨3 + 3, by omega⟩
        else 1 - point ⟨3 + 3, by omega⟩) *
      ((if index.val.testBit 1 then point ⟨3 + 4, by omega⟩
        else 1 - point ⟨3 + 4, by omega⟩) *
       (if index.val.testBit 0 then point ⟨3 + 5, by omega⟩
        else 1 - point ⟨3 + 5, by omega⟩))))) := by
  unfold suffixWeight6
  rw [prod_fin_six]
  rw [suffixBit_zero, suffixBit_one, suffixBit_two, suffixBit_three,
    suffixBit_four, suffixBit_five]
  simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod]

private theorem bigEndianBit_layout_x (index : Fin 48) (coordinate : Fin 10) :
    bigEndianBit (layoutRowFin (Fin.castAdd 48 index)) coordinate =
      ![true, true, true,
        index.val.testBit 5, index.val.testBit 4, index.val.testBit 3,
        index.val.testBit 2, index.val.testBit 1, index.val.testBit 0,
        false] coordinate := by
  have hsevenTwo : Nat.testBit 7 2 = true := by decide
  have hsevenOne : Nat.testBit 7 1 = true := by decide
  rw [bigEndianBit, layoutRowFin_x_val]
  rw [Nat.testBit_two_pow_mul_add 7 (by omega)]
  fin_cases coordinate <;>
    norm_num [testBit_twice_succ, hsevenTwo, hsevenOne]

private theorem bigEndianBit_layout_y (index : Fin 48) (coordinate : Fin 10) :
    bigEndianBit (layoutRowFin (Fin.natAdd 48 index)) coordinate =
      ![true, true, true,
        index.val.testBit 5, index.val.testBit 4, index.val.testBit 3,
        index.val.testBit 2, index.val.testBit 1, index.val.testBit 0,
        true] coordinate := by
  have hsevenTwo : Nat.testBit 7 2 = true := by decide
  have hsevenOne : Nat.testBit 7 1 = true := by decide
  rw [bigEndianBit, layoutRowFin_y_val]
  rw [Nat.testBit_two_pow_mul_add 7 (by omega)]
  fin_cases coordinate <;>
    norm_num [testBit_twice_add_one_succ, hsevenTwo, hsevenOne]

/-- Big-endian MLE weights at physical rows `896+2k` are the fixed three-one
prefix, the six cached suffix bits, and the final zero branch. -/
theorem mleRowWeight_layout_x
    {K : Type*} [CommRing K] (point : TranscriptPoint K) (index : Fin 48) :
    mleRowWeight point (layoutRowFin (Fin.castAdd 48 index)) =
      xPrefix point * suffixWeight6 point ⟨index.val, by omega⟩ := by
  have h0 : bigEndianBit (layoutRowFin (Fin.castAdd 48 index)) 0 = true := by
    simpa using bigEndianBit_layout_x index 0
  have h1 : bigEndianBit (layoutRowFin (Fin.castAdd 48 index)) 1 = true := by
    simpa using bigEndianBit_layout_x index 1
  have h2 : bigEndianBit (layoutRowFin (Fin.castAdd 48 index)) 2 = true := by
    simpa using bigEndianBit_layout_x index 2
  have h3 : bigEndianBit (layoutRowFin (Fin.castAdd 48 index)) 3 =
      index.val.testBit 5 := by simpa using bigEndianBit_layout_x index 3
  have h4 : bigEndianBit (layoutRowFin (Fin.castAdd 48 index)) 4 =
      index.val.testBit 4 := by simpa using bigEndianBit_layout_x index 4
  have h5 : bigEndianBit (layoutRowFin (Fin.castAdd 48 index)) 5 =
      index.val.testBit 3 := by simpa using bigEndianBit_layout_x index 5
  have h6 : bigEndianBit (layoutRowFin (Fin.castAdd 48 index)) 6 =
      index.val.testBit 2 := by simpa using bigEndianBit_layout_x index 6
  have h7 : bigEndianBit (layoutRowFin (Fin.castAdd 48 index)) 7 =
      index.val.testBit 1 := by simpa using bigEndianBit_layout_x index 7
  have h8 : bigEndianBit (layoutRowFin (Fin.castAdd 48 index)) 8 =
      index.val.testBit 0 := by simpa using bigEndianBit_layout_x index 8
  have h9 : bigEndianBit (layoutRowFin (Fin.castAdd 48 index)) 9 = false := by
    simpa using bigEndianBit_layout_x index 9
  unfold mleRowWeight
  rw [prod_fin_ten, suffixWeight6_explicit]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  unfold xPrefix
  simp only [Bool.false_eq_true, eq_self, if_false, if_true]
  ac_rfl

/-- The adjacent physical rows `897+2k` have the identical cached suffix and
the final one branch. -/
theorem mleRowWeight_layout_y
    {K : Type*} [CommRing K] (point : TranscriptPoint K) (index : Fin 48) :
    mleRowWeight point (layoutRowFin (Fin.natAdd 48 index)) =
      yPrefix point * suffixWeight6 point ⟨index.val, by omega⟩ := by
  have h0 : bigEndianBit (layoutRowFin (Fin.natAdd 48 index)) 0 = true := by
    simpa using bigEndianBit_layout_y index 0
  have h1 : bigEndianBit (layoutRowFin (Fin.natAdd 48 index)) 1 = true := by
    simpa using bigEndianBit_layout_y index 1
  have h2 : bigEndianBit (layoutRowFin (Fin.natAdd 48 index)) 2 = true := by
    simpa using bigEndianBit_layout_y index 2
  have h3 : bigEndianBit (layoutRowFin (Fin.natAdd 48 index)) 3 =
      index.val.testBit 5 := by simpa using bigEndianBit_layout_y index 3
  have h4 : bigEndianBit (layoutRowFin (Fin.natAdd 48 index)) 4 =
      index.val.testBit 4 := by simpa using bigEndianBit_layout_y index 4
  have h5 : bigEndianBit (layoutRowFin (Fin.natAdd 48 index)) 5 =
      index.val.testBit 3 := by simpa using bigEndianBit_layout_y index 5
  have h6 : bigEndianBit (layoutRowFin (Fin.natAdd 48 index)) 6 =
      index.val.testBit 2 := by simpa using bigEndianBit_layout_y index 6
  have h7 : bigEndianBit (layoutRowFin (Fin.natAdd 48 index)) 7 =
      index.val.testBit 1 := by simpa using bigEndianBit_layout_y index 7
  have h8 : bigEndianBit (layoutRowFin (Fin.natAdd 48 index)) 8 =
      index.val.testBit 0 := by simpa using bigEndianBit_layout_y index 8
  have h9 : bigEndianBit (layoutRowFin (Fin.natAdd 48 index)) 9 = true := by
    simpa using bigEndianBit_layout_y index 9
  unfold mleRowWeight
  rw [prod_fin_ten, suffixWeight6_explicit]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  unfold yPrefix
  simp only [Bool.false_eq_true, eq_self, if_false, if_true]
  ac_rfl

private theorem branch_from_bit {K : Type*} [CommRing K]
    (value : K) (index bit : Nat) :
    (if index / 2 ^ bit % 2 = 0 then 1 - value else value) =
      if index.testBit bit then value else 1 - value := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (index / 2 ^ bit) with hzero | hone
  · simp [hzero]
  · simp [hone]

/-- The generated recursion for its 64 cached words is exactly the six
big-endian suffix factors of the maintained row weight. -/
theorem suffixWeight6_eq_exactSuffixWeight
    (point : TranscriptPoint Tower) (index : Fin 64) :
    suffixWeight6 point index = exactSuffixWeight point index := by
  rw [suffixWeight6_explicit_raw]
  unfold exactSuffixWeight
  rw [suffixRec_succ point 5 index.val (by omega)]
  rw [suffixRec_succ point 4 (index.val / 2) (by omega)]
  rw [suffixRec_succ point 3 (index.val / 2 / 2) (by omega)]
  rw [suffixRec_succ point 2 (index.val / 2 / 2 / 2) (by omega)]
  rw [suffixRec_succ point 1 (index.val / 2 / 2 / 2 / 2) (by omega)]
  rw [suffixRec_succ point 0 (index.val / 2 / 2 / 2 / 2 / 2) (by omega)]
  have hbase :
      suffixRec point 0 (index.val / 2 / 2 / 2 / 2 / 2 / 2) = 1 := by
    unfold suffixRec
    rw [if_pos]
    omega
  rw [hbase]
  have hbit0 :
      (if index.val % 2 = 0 then 1 - point ⟨3 + 5, by omega⟩
        else point ⟨3 + 5, by omega⟩) =
        if index.val.testBit 0 then point ⟨3 + 5, by omega⟩
        else 1 - point ⟨3 + 5, by omega⟩ := by
    simpa using branch_from_bit (point ⟨3 + 5, by omega⟩) index.val 0
  have hbit1 :
      (if index.val / 2 % 2 = 0 then 1 - point ⟨3 + 4, by omega⟩
        else point ⟨3 + 4, by omega⟩) =
        if index.val.testBit 1 then point ⟨3 + 4, by omega⟩
        else 1 - point ⟨3 + 4, by omega⟩ := by
    simpa using branch_from_bit (point ⟨3 + 4, by omega⟩) index.val 1
  have hbit2 :
      (if index.val / 2 / 2 % 2 = 0 then 1 - point ⟨3 + 3, by omega⟩
        else point ⟨3 + 3, by omega⟩) =
        if index.val.testBit 2 then point ⟨3 + 3, by omega⟩
        else 1 - point ⟨3 + 3, by omega⟩ := by
    simpa [Nat.div_div_eq_div_mul] using
      branch_from_bit (point ⟨3 + 3, by omega⟩) index.val 2
  have hbit3 :
      (if index.val / 2 / 2 / 2 % 2 = 0 then 1 - point ⟨3 + 2, by omega⟩
        else point ⟨3 + 2, by omega⟩) =
        if index.val.testBit 3 then point ⟨3 + 2, by omega⟩
        else 1 - point ⟨3 + 2, by omega⟩ := by
    simpa [Nat.div_div_eq_div_mul] using
      branch_from_bit (point ⟨3 + 2, by omega⟩) index.val 3
  have hbit4 :
      (if index.val / 2 / 2 / 2 / 2 % 2 = 0 then 1 - point ⟨3 + 1, by omega⟩
        else point ⟨3 + 1, by omega⟩) =
        if index.val.testBit 4 then point ⟨3 + 1, by omega⟩
        else 1 - point ⟨3 + 1, by omega⟩ := by
    simpa [Nat.div_div_eq_div_mul] using
      branch_from_bit (point ⟨3 + 1, by omega⟩) index.val 4
  have hbit5 :
      (if index.val / 2 / 2 / 2 / 2 / 2 % 2 = 0 then 1 - point ⟨3 + 0, by omega⟩
        else point ⟨3 + 0, by omega⟩) =
        if index.val.testBit 5 then point ⟨3 + 0, by omega⟩
        else 1 - point ⟨3 + 0, by omega⟩ := by
    simpa [Nat.div_div_eq_div_mul] using
      branch_from_bit (point ⟨3 + 0, by omega⟩) index.val 5
  rw [hbit0, hbit1, hbit2, hbit3, hbit4, hbit5]
  simp only [one_mul, mul_assoc]

/-- Block diagonality of the maintained conversion, in the two directions not
needed by the generated conversion-entry theorem. -/
theorem deployedAConversion_xBlock_second_zero
    (ordinary : Fin 48 → Base) (natural : Fin 48) :
    deployedAConversion (liftBaseCoins (xBlockOrdinary ordinary))
        (secondBlockIndex natural) = 0 := by
  rw [deployedAConversion, Matrix.mulVecLin_apply]
  unfold Matrix.mulVec dotProduct
  change (∑ index : Fin (48 + 48),
      deployedAConversionMatrix (secondBlockIndex natural) index *
        liftBaseCoins (xBlockOrdinary ordinary) index) = 0
  rw [Fin.sum_univ_add]
  have hfirst :
      (∑ index : Fin 48,
        deployedAConversionMatrix (secondBlockIndex natural)
            (Fin.castAdd 48 index) *
          liftBaseCoins (xBlockOrdinary ordinary)
            (Fin.castAdd 48 index)) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    rw [show deployedAConversionMatrix (secondBlockIndex natural)
        (Fin.castAdd 48 index) = 0 by
      unfold deployedAConversionMatrix
      rw [if_neg]
      simp [secondBlockIndex, originalHalf]]
    simp
  have hsecond :
      (∑ index : Fin 48,
        deployedAConversionMatrix (secondBlockIndex natural)
            (Fin.natAdd 48 index) *
          liftBaseCoins (xBlockOrdinary ordinary)
            (Fin.natAdd 48 index)) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    simp [liftBaseCoins, xBlockOrdinary, ordinaryOfBlocks, originalHalf]
  rw [hfirst, hsecond, add_zero]

theorem deployedAConversion_yBlock_first_zero
    (ordinary : Fin 48 → Base) (natural : Fin 48) :
    deployedAConversion (liftBaseCoins (yBlockOrdinary ordinary))
        (firstBlockIndex natural) = 0 := by
  rw [deployedAConversion, Matrix.mulVecLin_apply]
  unfold Matrix.mulVec dotProduct
  change (∑ index : Fin (48 + 48),
      deployedAConversionMatrix (firstBlockIndex natural) index *
        liftBaseCoins (yBlockOrdinary ordinary) index) = 0
  rw [Fin.sum_univ_add]
  have hfirst :
      (∑ index : Fin 48,
        deployedAConversionMatrix (firstBlockIndex natural)
            (Fin.castAdd 48 index) *
          liftBaseCoins (yBlockOrdinary ordinary)
            (Fin.castAdd 48 index)) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    simp [liftBaseCoins, yBlockOrdinary, ordinaryOfBlocks, originalHalf]
  have hsecond :
      (∑ index : Fin 48,
        deployedAConversionMatrix (firstBlockIndex natural)
            (Fin.natAdd 48 index) *
          liftBaseCoins (yBlockOrdinary ordinary)
            (Fin.natAdd 48 index)) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    rw [show deployedAConversionMatrix (firstBlockIndex natural)
        (Fin.natAdd 48 index) = 0 by
      unfold deployedAConversionMatrix
      rw [if_neg]
      simp [firstBlockIndex, originalHalf]]
    simp
  rw [hfirst, hsecond, add_zero]

private noncomputable def convertedNatural (ordinary : Fin 48 → Base) :
    Fin 48 → Base :=
  (monomialToNatural Base 48).mulVec ordinary

private noncomputable def naturalWeightedDot
    (point : TranscriptPoint Tower) (natural : Fin 48 → Base) : Tower :=
  ∑ index : Fin 48,
    exactSuffixWeight point ⟨index.val, by omega⟩ *
      algebraMap Base Tower (natural index)

/-- Generic x/even-half evaluation of an aligned 96-coordinate vector. -/
private theorem multilinearEvalValue_aligned_x
    {K : Type*} [Field K] (point : TranscriptPoint K)
    (values : Fin (48 + 48) → K) (natural : Fin 48 → K)
    (hfirst : ∀ index, values (Fin.castAdd 48 index) = natural index)
    (hsecond : ∀ index, values (Fin.natAdd 48 index) = 0) :
    multilinearEvalValue point (alignedReserveEmbed K values) =
      xPrefix point *
        ∑ index : Fin 48,
          suffixWeight6 point ⟨index.val, by omega⟩ * natural index := by
  apply Eq.trans (multilinearEvalValue_alignedReserveEmbed point values)
  change (∑ index : Fin (48 + 48),
      mleRowWeight point (layoutRowFin index) * values index) = _
  rw [Fin.sum_univ_add]
  have hx :
      (∑ index : Fin 48,
        mleRowWeight point (layoutRowFin (Fin.castAdd 48 index)) *
          values (Fin.castAdd 48 index)) =
        xPrefix point *
          ∑ index : Fin 48,
            suffixWeight6 point ⟨index.val, by omega⟩ * natural index := by
    simp_rw [mleRowWeight_layout_x, hfirst]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ac_rfl
  have hy :
      (∑ index : Fin 48,
        mleRowWeight point (layoutRowFin (Fin.natAdd 48 index)) *
          values (Fin.natAdd 48 index)) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    rw [hsecond, mul_zero]
  rw [hx, hy, add_zero]

/-- Generic y/odd-half evaluation of an aligned 96-coordinate vector. -/
private theorem multilinearEvalValue_aligned_y
    {K : Type*} [Field K] (point : TranscriptPoint K)
    (values : Fin (48 + 48) → K) (natural : Fin 48 → K)
    (hfirst : ∀ index, values (Fin.castAdd 48 index) = 0)
    (hsecond : ∀ index, values (Fin.natAdd 48 index) = natural index) :
    multilinearEvalValue point (alignedReserveEmbed K values) =
      yPrefix point *
        ∑ index : Fin 48,
          suffixWeight6 point ⟨index.val, by omega⟩ * natural index := by
  apply Eq.trans (multilinearEvalValue_alignedReserveEmbed point values)
  change (∑ index : Fin (48 + 48),
      mleRowWeight point (layoutRowFin index) * values index) = _
  rw [Fin.sum_univ_add]
  have hx :
      (∑ index : Fin 48,
        mleRowWeight point (layoutRowFin (Fin.castAdd 48 index)) *
          values (Fin.castAdd 48 index)) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    rw [hfirst, mul_zero]
  have hy :
      (∑ index : Fin 48,
        mleRowWeight point (layoutRowFin (Fin.natAdd 48 index)) *
          values (Fin.natAdd 48 index)) =
        yPrefix point *
          ∑ index : Fin 48,
            suffixWeight6 point ⟨index.val, by omega⟩ * natural index := by
    simp_rw [mleRowWeight_layout_y, hsecond]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ac_rfl
  rw [hx, hy, zero_add]

/-- Explicit aligned-map form of the x/p terminal calculation. -/
private theorem multilinearEvalValue_xBlock_raw
    (point : TranscriptPoint Tower) (ordinary : Fin 48 → Base) :
    multilinearEvalValue point
        (alignedReserveEmbed Tower
          (deployedAConversion (liftBaseCoins (xBlockOrdinary ordinary)))) =
      xPrefix point * naturalWeightedDot point (convertedNatural ordinary) := by
  calc
    _ = xPrefix point *
          ∑ index : Fin 48,
            suffixWeight6 point ⟨index.val, by omega⟩ *
              algebraMap Base Tower (convertedNatural ordinary index) := by
      apply multilinearEvalValue_aligned_x
      · intro index
        rw [show Fin.castAdd 48 index = firstBlockIndex index by rfl]
        exact deployedAConversion_xBlock ordinary index
      · intro index
        rw [show Fin.natAdd 48 index = secondBlockIndex index by rfl]
        exact deployedAConversion_xBlock_second_zero ordinary index
    _ = _ := by
      unfold naturalWeightedDot
      simp_rw [suffixWeight6_eq_exactSuffixWeight]

/-- Explicit aligned-map form of the y/q terminal calculation. -/
private theorem multilinearEvalValue_yBlock_raw
    (point : TranscriptPoint Tower) (ordinary : Fin 48 → Base) :
    multilinearEvalValue point
        (alignedReserveEmbed Tower
          (deployedAConversion (liftBaseCoins (yBlockOrdinary ordinary)))) =
      yPrefix point * naturalWeightedDot point (convertedNatural ordinary) := by
  calc
    _ = yPrefix point *
          ∑ index : Fin 48,
            suffixWeight6 point ⟨index.val, by omega⟩ *
              algebraMap Base Tower (convertedNatural ordinary index) := by
      apply multilinearEvalValue_aligned_y
      · intro index
        rw [show Fin.castAdd 48 index = firstBlockIndex index by rfl]
        exact deployedAConversion_yBlock_first_zero ordinary index
      · intro index
        rw [show Fin.natAdd 48 index = secondBlockIndex index by rfl]
        exact deployedAConversion_yBlock ordinary index
    _ = _ := by
      unfold naturalWeightedDot
      simp_rw [suffixWeight6_eq_exactSuffixWeight]

private theorem exactQM31Limb_eq_towerCoordinates
    (value : Tower) (limb : Fin 4) :
    exactQM31Limb value limb = towerCoordinates value limb := by
  fin_cases limb <;> rfl

private theorem exactQM31Limb_algebraMap_mul
    (scalar : Base) (value : Tower) (limb : Fin 4) :
    exactQM31Limb (algebraMap Base Tower scalar * value) limb =
      scalar * exactQM31Limb value limb := by
  rw [exactQM31Limb_eq_towerCoordinates,
    exactQM31Limb_eq_towerCoordinates]
  calc
    towerCoordinates ((algebraMap Base Tower) scalar * value) limb =
        towerCoordinatesLinear (scalar • value) limb := by
      simp only [Algebra.smul_def]
      change towerCoordinates ((algebraMap Base Tower) scalar * value) limb =
        towerCoordinates ((algebraMap Base Tower) scalar * value) limb
      rfl
    _ = (scalar • towerCoordinatesLinear value) limb :=
      congrFun (towerCoordinatesLinear.map_smul scalar value) limb
    _ = scalar * towerCoordinates value limb := by
      simp only [Pi.smul_apply, smul_eq_mul]
      change scalar * towerCoordinates value limb =
        scalar * towerCoordinates value limb
      rfl

private theorem exactQM31Limb_mul_algebraMap
    (value : Tower) (scalar : Base) (limb : Fin 4) :
    exactQM31Limb (value * algebraMap Base Tower scalar) limb =
      scalar * exactQM31Limb value limb := by
  rw [mul_comm]
  exact exactQM31Limb_algebraMap_mul scalar value limb

private theorem exactQM31Limb_sum
    {ι : Type*} [Fintype ι] (values : ι → Tower) (limb : Fin 4) :
    exactQM31Limb (∑ index, values index) limb =
      ∑ index, exactQM31Limb (values index) limb := by
  simp_rw [exactQM31Limb_eq_towerCoordinates]
  change towerCoordinatesLinear (∑ index, values index) limb =
    ∑ index, towerCoordinatesLinear (values index) limb
  rw [map_sum]
  simp only [Finset.sum_apply]

private theorem shiftedExact_zero_coordinate_sum
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 0 index *
        exactQM31Limb (weightsToExact localWeights
          ⟨index.val, by omega⟩) limb) =
      exactDotLimbFor localWeights 0 0 limb.val := by
  simp_rw [shiftedExact_zero]
  norm_num [exactDotLimbFor_zero, shiftedExact_zero, Fin.sum_univ_succ,
    Finset.sum_range_succ, evenVector, evenCoefficients0,
    exactWeightWordFor]
  ring

private theorem shiftedExact_one_coordinate_sum
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 1 index *
        exactQM31Limb (weightsToExact localWeights
          ⟨index.val, by omega⟩) limb) =
      exactDotLimbFor localWeights 1 0 limb.val := by
  simp_rw [shiftedExact_one_oddVector]
  norm_num [exactDotLimbFor_1, shiftedExact_one_oddVector,
    Fin.sum_univ_succ, Finset.sum_range_succ, oddVector,
    evenCoefficients0, exactWeightWordFor]
  ring

private theorem shiftedExact_two_coordinate_sum
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 2 index *
        exactQM31Limb (weightsToExact localWeights
          ⟨index.val, by omega⟩) limb) =
      exactDotLimbFor localWeights 2 0 limb.val := by
  simp_rw [shiftedExact_two_evenVector]
  norm_num [exactDotLimbFor_2, shiftedExact_two_evenVector,
    Fin.sum_univ_succ, Finset.sum_range_succ, evenVector,
    evenCoefficients2, exactWeightWordFor]
  ring

private theorem shiftedExact_three_coordinate_sum
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 3 index *
        exactQM31Limb (weightsToExact localWeights
          ⟨index.val, by omega⟩) limb) =
      exactDotLimbFor localWeights 3 0 limb.val := by
  simp_rw [shiftedExact_three]
  norm_num [exactDotLimbFor_3, shiftedExact_three,
    Fin.sum_univ_succ, Finset.sum_range_succ, oddVector,
    evenCoefficients2, exactWeightWordFor]
  ring

private theorem shiftedExact_four_coordinate_sum
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 4 index *
        exactQM31Limb (weightsToExact localWeights
          ⟨index.val, by omega⟩) limb) =
      exactDotLimbFor localWeights 4 0 limb.val := by
  simp_rw [shiftedExact_four]
  norm_num [exactDotLimbFor_4, shiftedExact_four,
    Fin.sum_univ_succ, Finset.sum_range_succ, evenVector,
    evenCoefficients4, exactWeightWordFor]
  ring

private theorem shiftedExact_five_coordinate_sum
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 5 index *
        exactQM31Limb (weightsToExact localWeights
          ⟨index.val, by omega⟩) limb) =
      exactDotLimbFor localWeights 5 0 limb.val := by
  simp_rw [shiftedExact_five]
  norm_num [exactDotLimbFor_5, shiftedExact_five,
    Fin.sum_univ_succ, Finset.sum_range_succ, oddVector,
    evenCoefficients4, exactWeightWordFor]
  ring

private theorem shiftedExact_six_coordinate_sum
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 6 index *
        exactQM31Limb (weightsToExact localWeights
          ⟨index.val, by omega⟩) limb) =
      exactDotLimbFor localWeights 6 0 limb.val := by
  simp_rw [shiftedExact_six]
  norm_num [exactDotLimbFor_6, shiftedExact_six,
    Fin.sum_univ_succ, Finset.sum_range_succ, evenVector,
    evenCoefficients6, exactWeightWordFor]
  ring

private theorem shiftedExact_seven_coordinate_sum
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 7 index *
        exactQM31Limb (weightsToExact localWeights
          ⟨index.val, by omega⟩) limb) =
      exactDotLimbFor localWeights 7 0 limb.val := by
  simp_rw [shiftedExact_seven]
  norm_num [exactDotLimbFor_7, shiftedExact_seven,
    Fin.sum_univ_succ, Finset.sum_range_succ, oddVector,
    evenCoefficients6, exactWeightWordFor]
  ring

private theorem shiftedExact_eight_coordinate_sum
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 8 index *
        exactQM31Limb (weightsToExact localWeights
          ⟨index.val, by omega⟩) limb) =
      exactDotLimbFor localWeights 8 0 limb.val := by
  simp_rw [shiftedExact_eight]
  norm_num [exactDotLimbFor_8, shiftedExact_eight,
    Fin.sum_univ_succ, Finset.sum_range_succ, evenVector,
    evenCoefficients8, exactWeightWordFor]
  ring

private theorem shiftedExact_nine_coordinate_sum
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 9 index *
        exactQM31Limb (weightsToExact localWeights
          ⟨index.val, by omega⟩) limb) =
      exactDotLimbFor localWeights 9 0 limb.val := by
  simp_rw [shiftedExact_nine]
  norm_num [exactDotLimbFor_9, shiftedExact_nine,
    Fin.sum_univ_succ, Finset.sum_range_succ, oddVector,
    evenCoefficients8, exactWeightWordFor]
  ring

private theorem shiftedExact_ten_coordinate_sum
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 10 index *
        exactQM31Limb (weightsToExact localWeights
          ⟨index.val, by omega⟩) limb) =
      exactDotLimbFor localWeights 10 0 limb.val := by
  simp_rw [shiftedExact_ten]
  norm_num [exactDotLimbFor_10, shiftedExact_ten,
    Fin.sum_univ_succ, Finset.sum_range_succ, evenVector,
    evenCoefficients10, exactWeightWordFor]
  ring

private theorem shiftedExact_eleven_coordinate_sum
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 11 index *
        exactQM31Limb (weightsToExact localWeights
          ⟨index.val, by omega⟩) limb) =
      exactDotLimbFor localWeights 11 0 limb.val := by
  simp_rw [shiftedExact_eleven]
  norm_num [exactDotLimbFor_11, shiftedExact_eleven,
    Fin.sum_univ_succ, Finset.sum_range_succ, oddVector,
    evenCoefficients10, exactWeightWordFor]
  ring

private theorem shiftedExact_coordinate_sum
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (shift : Fin 12) (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact shift.val index *
        exactQM31Limb (weightsToExact localWeights
          ⟨index.val, by omega⟩) limb) =
      exactDotLimbFor localWeights shift 0 limb.val := by
  fin_cases shift
  · exact shiftedExact_zero_coordinate_sum localWeights limb
  · exact shiftedExact_one_coordinate_sum localWeights limb
  · exact shiftedExact_two_coordinate_sum localWeights limb
  · exact shiftedExact_three_coordinate_sum localWeights limb
  · exact shiftedExact_four_coordinate_sum localWeights limb
  · exact shiftedExact_five_coordinate_sum localWeights limb
  · exact shiftedExact_six_coordinate_sum localWeights limb
  · exact shiftedExact_seven_coordinate_sum localWeights limb
  · exact shiftedExact_eight_coordinate_sum localWeights limb
  · exact shiftedExact_nine_coordinate_sum localWeights limb
  · exact shiftedExact_ten_coordinate_sum localWeights limb
  · exact shiftedExact_eleven_coordinate_sum localWeights limb

private theorem exactQM31Limb_exactDotFor
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (shift : Fin 12) (mask : Nat) (limb : Fin 4) :
    exactQM31Limb (exactDotFor localWeights shift mask) limb =
      exactDotLimbFor localWeights shift mask limb.val := by
  fin_cases limb <;> rfl

private theorem naturalWeightedDot_shiftedExact
    (point : TranscriptPoint Tower)
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (shift : Fin 12)
    (hweights : weightsToExact localWeights = exactSuffixWeight point) :
    naturalWeightedDot point (shiftedExact shift.val) =
      exactDotFor localWeights shift 0 := by
  apply towerCoordinates_injective
  funext limb
  rw [← exactQM31Limb_eq_towerCoordinates,
    ← exactQM31Limb_eq_towerCoordinates]
  unfold naturalWeightedDot
  rw [exactQM31Limb_sum
    (fun index : Fin 48 =>
      exactSuffixWeight point ⟨index.val, by omega⟩ *
        algebraMap Base Tower (shiftedExact shift.val index)) limb]
  simp_rw [← hweights]
  simp_rw [exactQM31Limb_mul_algebraMap]
  rw [exactQM31Limb_exactDotFor]
  exact shiftedExact_coordinate_sum localWeights shift limb

/-- The generated sparse direction and the maintained ordinary conversion
are the same vector for every one of the twelve concrete kernel shifts. -/
theorem convertedNatural_maintained_shift_eq_shiftedExact
    (shift : Fin 12) :
    convertedNatural
        (ordinaryShiftIter shift.val maintainedConcreteOrdinary) =
      shiftedExact shift.val := by
  letI : NeZero (2 : Base) := ⟨by decide⟩
  have hkernelModel :
      GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary kernel =
        maintainedConcreteOrdinary :=
    runtimeKernelMatchesMaintainedConcreteOrdinary
  have hbase :
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
          baseDirection =
        convert
          (GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary
            kernel) :=
    baseDirection_source_exact.trans
      (GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion_eq_convert
        kernel)
  change convert (ordinaryShiftIter shift.val maintainedConcreteOrdinary) = _
  rw [← hkernelModel]
  calc
    convert (ordinaryShiftIter shift.val
        (GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary
          kernel)) =
        sparseShiftIter shift.val
          (convert
            (GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary
              kernel)) :=
      (goodA_complete_shift_chain
        (GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary kernel)
        (GoodMatricesCurrent.SourceExtractedGoodAModelBridge.evenKernelOrdinary_supportedBelow
          kernel) shift.val (by omega)).symm
    _ = sparseShiftIter shift.val
        (GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
          baseDirection) := by
      exact congrArg (sparseShiftIter shift.val) hbase.symm
    _ = shiftedExact shift.val := rfl

private theorem ordinaryShiftIter_apply
    (steps : Nat) (ordinary : Fin 48 → Base) (index : Fin 48) :
    ordinaryShiftIter steps ordinary index =
      if h : steps ≤ index.val then
        ordinary ⟨index.val - steps, by omega⟩
      else 0 := by
  induction steps generalizing index with
  | zero => simp [ordinaryShiftIter]
  | succ steps ih =>
      rw [ordinaryShiftIter]
      rcases Fin.eq_zero_or_eq_succ index with rfl | ⟨previous, rfl⟩
      · simp [ordinaryShift]
      · change ordinaryShiftIter steps ordinary (sourceIndex previous) = _
        rw [ih]
        change (if h : steps ≤ previous.val then
            ordinary ⟨previous.val - steps, by omega⟩ else 0) =
          if h : steps + 1 ≤ previous.val + 1 then
            ordinary ⟨previous.val + 1 - (steps + 1), by omega⟩ else 0
        by_cases h : steps ≤ previous.val
        · rw [dif_pos h, dif_pos (by omega)]
          congr 1
          apply Fin.ext
          simp
        · rw [dif_neg h, dif_neg (by omega)]

private theorem polynomialBlock_kernelShift_eq_ordinaryShift_sub
    (steps : Nat) (index : Fin 48) :
    polynomialBlock
        (AspisV5ComponentARankCompletion.kernelShift
          ConcreteProbeWitness.naturalQ18 steps) index =
      ordinaryShiftIter steps maintainedConcreteOrdinary index -
        maintainedConcreteOrdinary index := by
  unfold polynomialBlock AspisV5ComponentARankCompletion.kernelShift
    maintainedConcreteOrdinary
  rw [mul_sub, mul_one, coeff_sub, coeff_mul_X_pow']
  rw [ordinaryShiftIter_apply]
  rfl

private theorem polynomialBlock_kernelShift_eq_ordinaryShift_sub_fun
    (steps : Nat) :
    polynomialBlock
        (AspisV5ComponentARankCompletion.kernelShift
          ConcreteProbeWitness.naturalQ18 steps) =
      ordinaryShiftIter steps maintainedConcreteOrdinary -
        maintainedConcreteOrdinary := by
  funext index
  exact polynomialBlock_kernelShift_eq_ordinaryShift_sub steps index

private theorem convertedNatural_sub
    (left right : Fin 48 → Base) :
    convertedNatural (left - right) =
      convertedNatural left - convertedNatural right := by
  unfold convertedNatural
  exact Matrix.mulVec_sub _ _ _

private theorem naturalWeightedDot_sub
    (point : TranscriptPoint Tower) (left right : Fin 48 → Base) :
    naturalWeightedDot point (left - right) =
      naturalWeightedDot point left - naturalWeightedDot point right := by
  unfold naturalWeightedDot
  simp_rw [Pi.sub_apply, map_sub (algebraMap Base Tower), mul_sub]
  rw [Finset.sum_sub_distrib]

private theorem convertedNatural_maintained_eq_shiftedExact_zero :
    convertedNatural maintainedConcreteOrdinary = shiftedExact 0 := by
  simpa [ordinaryShiftIter] using
    convertedNatural_maintained_shift_eq_shiftedExact (0 : Fin 12)

private theorem aligned_x_kernelShift_eval
    (point : TranscriptPoint Tower)
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (shift : Fin 12)
    (hweights : weightsToExact localWeights = exactSuffixWeight point) :
    multilinearEvalValue point
        (alignedReserveEmbed Tower
          (deployedAConversion
            (liftBaseCoins
              (xBlockOrdinary
                (polynomialBlock
                  (AspisV5ComponentARankCompletion.kernelShift
                    ConcreteProbeWitness.naturalQ18 shift.val)))))) =
      xPrefix point *
        (exactDotFor localWeights shift 0 -
          exactDotFor localWeights 0 0) := by
  rw [multilinearEvalValue_xBlock_raw]
  rw [polynomialBlock_kernelShift_eq_ordinaryShift_sub_fun]
  rw [convertedNatural_sub, naturalWeightedDot_sub]
  rw [convertedNatural_maintained_shift_eq_shiftedExact,
    convertedNatural_maintained_eq_shiftedExact_zero]
  rw [naturalWeightedDot_shiftedExact point localWeights shift hweights]
  have hzero : naturalWeightedDot point (shiftedExact 0) =
      exactDotFor localWeights 0 0 := by
    simpa using naturalWeightedDot_shiftedExact point localWeights
      (0 : Fin 12) hweights
  rw [hzero]

private theorem aligned_y_kernelShift_eval
    (point : TranscriptPoint Tower)
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (shift : Fin 12)
    (hweights : weightsToExact localWeights = exactSuffixWeight point) :
    multilinearEvalValue point
        (alignedReserveEmbed Tower
          (deployedAConversion
            (liftBaseCoins
              (yBlockOrdinary
                (polynomialBlock
                  (AspisV5ComponentARankCompletion.kernelShift
                    ConcreteProbeWitness.naturalQ18 shift.val)))))) =
      yPrefix point *
        (exactDotFor localWeights shift 0 -
          exactDotFor localWeights 0 0) := by
  rw [multilinearEvalValue_yBlock_raw]
  rw [polynomialBlock_kernelShift_eq_ordinaryShift_sub_fun]
  rw [convertedNatural_sub, naturalWeightedDot_sub]
  rw [convertedNatural_maintained_shift_eq_shiftedExact,
    convertedNatural_maintained_eq_shiftedExact_zero]
  rw [naturalWeightedDot_shiftedExact point localWeights shift hweights]
  have hzero : naturalWeightedDot point (shiftedExact 0) =
      exactDotFor localWeights 0 0 := by
    simpa using naturalWeightedDot_shiftedExact point localWeights
      (0 : Fin 12) hweights
  rw [hzero]

private theorem concretePoint_exact :
    ConcreteProbeWitness.probePoint =
      GoodMatricesCurrent.SourceExtractedTerminalWeights.pointToExact point := by
  funext coordinate
  fin_cases coordinate <;> decide

private theorem concreteSuccessor_exact :
    deployedSuccessorPoint ConcreteProbeWitness.probePoint =
      GoodMatricesCurrent.SourceExtractedTerminalWeights.pointToExact
        successor := by
  rw [concretePoint_exact]
  exact successor_exact.symm

private theorem concreteWeights_exact :
    weightsToExact weights =
      exactSuffixWeight
        (GoodMatricesCurrent.SourceExtractedTerminalWeights.pointToExact
          point) := by
  funext index
  fin_cases index <;> decide

private theorem xPrefix_pointToExact
    (localPoint : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalPoint) :
    xPrefix
        (GoodMatricesCurrent.SourceExtractedTerminalWeights.pointToExact
          localPoint) =
      exactAPFor localPoint := by
  rfl

private theorem yPrefix_pointToExact
    (localPoint : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalPoint) :
    yPrefix
        (GoodMatricesCurrent.SourceExtractedTerminalWeights.pointToExact
          localPoint) =
      exactAQFor localPoint := by
  rfl

private def xorSixIndex (index : Fin 48) : Fin 64 :=
  ⟨Nat.xor index.val 6, mask_six_bound index.val index.isLt⟩

private theorem exactDotLimbFor_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (shift : Fin 12) (limb : Fin 4) :
    exactDotLimbFor localWeights shift 6 limb.val =
      ∑ logical ∈ Finset.range (19 + shift.val / 2),
        if hindex : shift.val % 2 + 2 * logical < 48 then
          shiftedExact shift.val
              ⟨shift.val % 2 + 2 * logical, hindex⟩ *
            exactQM31Limb
              (weightsToExact localWeights
                (xorSixIndex
                  ⟨shift.val % 2 + 2 * logical, hindex⟩)) limb
        else 0 := by
  unfold exactDotLimbFor
  apply Finset.sum_congr rfl
  intro logical _
  split
  next hindex =>
    unfold exactWeightWordFor xorSixIndex
    rw [dif_pos (mask_six_bound _ hindex), dif_pos limb.isLt]
  next _ => rfl

private theorem shiftedExact_zero_coordinate_sum_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 0 index *
        exactQM31Limb (weightsToExact localWeights (xorSixIndex index)) limb) =
      exactDotLimbFor localWeights 0 6 limb.val := by
  simp_rw [shiftedExact_zero]
  rw [exactDotLimbFor_xorSix]
  norm_num [shiftedExact_zero, Fin.sum_univ_succ,
    Finset.sum_range_succ, evenVector, evenCoefficients0,
    xorSixIndex]
  ring

private theorem shiftedExact_one_coordinate_sum_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 1 index *
        exactQM31Limb (weightsToExact localWeights (xorSixIndex index)) limb) =
      exactDotLimbFor localWeights 1 6 limb.val := by
  simp_rw [shiftedExact_one_oddVector]
  rw [exactDotLimbFor_xorSix]
  norm_num [shiftedExact_one_oddVector,
    Fin.sum_univ_succ, Finset.sum_range_succ, oddVector,
    evenCoefficients0, xorSixIndex]
  ring

private theorem shiftedExact_two_coordinate_sum_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 2 index *
        exactQM31Limb (weightsToExact localWeights (xorSixIndex index)) limb) =
      exactDotLimbFor localWeights 2 6 limb.val := by
  simp_rw [shiftedExact_two_evenVector]
  rw [exactDotLimbFor_xorSix]
  norm_num [shiftedExact_two_evenVector,
    Fin.sum_univ_succ, Finset.sum_range_succ, evenVector,
    evenCoefficients2, xorSixIndex]
  ring

private theorem shiftedExact_three_coordinate_sum_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 3 index *
        exactQM31Limb (weightsToExact localWeights (xorSixIndex index)) limb) =
      exactDotLimbFor localWeights 3 6 limb.val := by
  simp_rw [shiftedExact_three]
  rw [exactDotLimbFor_xorSix]
  norm_num [shiftedExact_three,
    Fin.sum_univ_succ, Finset.sum_range_succ, oddVector,
    evenCoefficients2, xorSixIndex]
  ring

private theorem shiftedExact_four_coordinate_sum_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 4 index *
        exactQM31Limb (weightsToExact localWeights (xorSixIndex index)) limb) =
      exactDotLimbFor localWeights 4 6 limb.val := by
  simp_rw [shiftedExact_four]
  rw [exactDotLimbFor_xorSix]
  norm_num [shiftedExact_four,
    Fin.sum_univ_succ, Finset.sum_range_succ, evenVector,
    evenCoefficients4, xorSixIndex]
  ring

private theorem shiftedExact_five_coordinate_sum_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 5 index *
        exactQM31Limb (weightsToExact localWeights (xorSixIndex index)) limb) =
      exactDotLimbFor localWeights 5 6 limb.val := by
  simp_rw [shiftedExact_five]
  rw [exactDotLimbFor_xorSix]
  norm_num [shiftedExact_five,
    Fin.sum_univ_succ, Finset.sum_range_succ, oddVector,
    evenCoefficients4, xorSixIndex]
  ring

private theorem shiftedExact_six_coordinate_sum_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 6 index *
        exactQM31Limb (weightsToExact localWeights (xorSixIndex index)) limb) =
      exactDotLimbFor localWeights 6 6 limb.val := by
  simp_rw [shiftedExact_six]
  rw [exactDotLimbFor_xorSix]
  norm_num [shiftedExact_six,
    Fin.sum_univ_succ, Finset.sum_range_succ, evenVector,
    evenCoefficients6, xorSixIndex]
  ring

private theorem shiftedExact_seven_coordinate_sum_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 7 index *
        exactQM31Limb (weightsToExact localWeights (xorSixIndex index)) limb) =
      exactDotLimbFor localWeights 7 6 limb.val := by
  simp_rw [shiftedExact_seven]
  rw [exactDotLimbFor_xorSix]
  norm_num [shiftedExact_seven,
    Fin.sum_univ_succ, Finset.sum_range_succ, oddVector,
    evenCoefficients6, xorSixIndex]
  ring

private theorem shiftedExact_eight_coordinate_sum_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 8 index *
        exactQM31Limb (weightsToExact localWeights (xorSixIndex index)) limb) =
      exactDotLimbFor localWeights 8 6 limb.val := by
  simp_rw [shiftedExact_eight]
  rw [exactDotLimbFor_xorSix]
  norm_num [shiftedExact_eight,
    Fin.sum_univ_succ, Finset.sum_range_succ, evenVector,
    evenCoefficients8, xorSixIndex]
  ring

private theorem shiftedExact_nine_coordinate_sum_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 9 index *
        exactQM31Limb (weightsToExact localWeights (xorSixIndex index)) limb) =
      exactDotLimbFor localWeights 9 6 limb.val := by
  simp_rw [shiftedExact_nine]
  rw [exactDotLimbFor_xorSix]
  norm_num [shiftedExact_nine,
    Fin.sum_univ_succ, Finset.sum_range_succ, oddVector,
    evenCoefficients8, xorSixIndex]
  ring

private theorem shiftedExact_ten_coordinate_sum_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 10 index *
        exactQM31Limb (weightsToExact localWeights (xorSixIndex index)) limb) =
      exactDotLimbFor localWeights 10 6 limb.val := by
  simp_rw [shiftedExact_ten]
  rw [exactDotLimbFor_xorSix]
  norm_num [shiftedExact_ten,
    Fin.sum_univ_succ, Finset.sum_range_succ, evenVector,
    evenCoefficients10, xorSixIndex]
  ring

private theorem shiftedExact_eleven_coordinate_sum_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact 11 index *
        exactQM31Limb (weightsToExact localWeights (xorSixIndex index)) limb) =
      exactDotLimbFor localWeights 11 6 limb.val := by
  simp_rw [shiftedExact_eleven]
  rw [exactDotLimbFor_xorSix]
  norm_num [shiftedExact_eleven,
    Fin.sum_univ_succ, Finset.sum_range_succ, oddVector,
    evenCoefficients10, xorSixIndex]
  ring

private theorem shiftedExact_coordinate_sum_xorSix
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (shift : Fin 12) (limb : Fin 4) :
    (∑ index : Fin 48,
      shiftedExact shift.val index *
        exactQM31Limb (weightsToExact localWeights (xorSixIndex index)) limb) =
      exactDotLimbFor localWeights shift 6 limb.val := by
  fin_cases shift
  · exact shiftedExact_zero_coordinate_sum_xorSix localWeights limb
  · exact shiftedExact_one_coordinate_sum_xorSix localWeights limb
  · exact shiftedExact_two_coordinate_sum_xorSix localWeights limb
  · exact shiftedExact_three_coordinate_sum_xorSix localWeights limb
  · exact shiftedExact_four_coordinate_sum_xorSix localWeights limb
  · exact shiftedExact_five_coordinate_sum_xorSix localWeights limb
  · exact shiftedExact_six_coordinate_sum_xorSix localWeights limb
  · exact shiftedExact_seven_coordinate_sum_xorSix localWeights limb
  · exact shiftedExact_eight_coordinate_sum_xorSix localWeights limb
  · exact shiftedExact_nine_coordinate_sum_xorSix localWeights limb
  · exact shiftedExact_ten_coordinate_sum_xorSix localWeights limb
  · exact shiftedExact_eleven_coordinate_sum_xorSix localWeights limb

private theorem naturalWeightedDot_shiftedExact_xorSix
    (point : TranscriptPoint Tower)
    (localWeights : GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights)
    (shift : Fin 12)
    (hweights : ∀ index : Fin 48,
      exactSuffixWeight point ⟨index.val, by omega⟩ =
        weightsToExact localWeights (xorSixIndex index)) :
    naturalWeightedDot point (shiftedExact shift.val) =
      exactDotFor localWeights shift 6 := by
  apply towerCoordinates_injective
  funext limb
  rw [← exactQM31Limb_eq_towerCoordinates,
    ← exactQM31Limb_eq_towerCoordinates]
  unfold naturalWeightedDot
  rw [exactQM31Limb_sum
    (fun index : Fin 48 =>
      exactSuffixWeight point ⟨index.val, by omega⟩ *
        algebraMap Base Tower (shiftedExact shift.val index)) limb]
  simp_rw [hweights]
  simp_rw [exactQM31Limb_mul_algebraMap]
  rw [exactQM31Limb_exactDotFor]
  exact shiftedExact_coordinate_sum_xorSix localWeights shift limb

private theorem concreteXorWeights_exact (index : Fin 48) :
    exactSuffixWeight
        (deployedXor12Point ConcreteProbeWitness.probePoint)
        ⟨index.val, by omega⟩ =
      weightsToExact weights (xorSixIndex index) := by
  rw [concretePoint_exact]
  fin_cases index <;> decide

/-- Maintained x-block terminal value at the concrete base point. -/
theorem aligned_x_kernelShift_eval_base (shift : Fin 12) :
    multilinearEvalValue ConcreteProbeWitness.probePoint
        (alignedReserveEmbed Tower
          (deployedAConversion
            (liftBaseCoins
              (xBlockOrdinary
                (polynomialBlock
                  (AspisV5ComponentARankCompletion.kernelShift
                    ConcreteProbeWitness.naturalQ18 shift.val)))))) =
      baseAPExact * (baseDotsExact shift - baseDotsExact 0) := by
  rw [concretePoint_exact]
  rw [aligned_x_kernelShift_eval _ weights shift concreteWeights_exact]
  rw [xPrefix_pointToExact, point_aP_exact]
  rw [show exactDotFor weights shift 0 = baseDotsExact shift by
      exact congrFun baseDots_exact shift]
  rw [show exactDotFor weights 0 0 = baseDotsExact 0 by
      exact congrFun baseDots_exact 0]

/-- Maintained y-block terminal value at the concrete base point. -/
theorem aligned_y_kernelShift_eval_base (shift : Fin 12) :
    multilinearEvalValue ConcreteProbeWitness.probePoint
        (alignedReserveEmbed Tower
          (deployedAConversion
            (liftBaseCoins
              (yBlockOrdinary
                (polynomialBlock
                  (AspisV5ComponentARankCompletion.kernelShift
                    ConcreteProbeWitness.naturalQ18 shift.val)))))) =
      baseAQExact * (baseDotsExact shift - baseDotsExact 0) := by
  rw [concretePoint_exact]
  rw [aligned_y_kernelShift_eval _ weights shift concreteWeights_exact]
  rw [yPrefix_pointToExact, point_aQ_exact]
  rw [show exactDotFor weights shift 0 = baseDotsExact shift by
      exact congrFun baseDots_exact shift]
  rw [show exactDotFor weights 0 0 = baseDotsExact 0 by
      exact congrFun baseDots_exact 0]

/-- Maintained x-block terminal value at the concrete successor point. -/
theorem aligned_x_kernelShift_eval_successor (shift : Fin 12) :
    multilinearEvalValue
        (deployedSuccessorPoint ConcreteProbeWitness.probePoint)
        (alignedReserveEmbed Tower
          (deployedAConversion
            (liftBaseCoins
              (xBlockOrdinary
                (polynomialBlock
                  (AspisV5ComponentARankCompletion.kernelShift
                    ConcreteProbeWitness.naturalQ18 shift.val)))))) =
      successorAPExact *
        (successorDotsExact shift - successorDotsExact 0) := by
  rw [concreteSuccessor_exact]
  rw [aligned_x_kernelShift_eval _ successorWeights shift
    successorWeights_exact]
  rw [xPrefix_pointToExact, successor_aP_exact]
  rw [show exactDotFor successorWeights shift 0 = successorDotsExact shift by
      exact congrFun successorDots_exact shift]
  rw [show exactDotFor successorWeights 0 0 = successorDotsExact 0 by
      exact congrFun successorDots_exact 0]

/-- Maintained y-block terminal value at the concrete successor point. -/
theorem aligned_y_kernelShift_eval_successor (shift : Fin 12) :
    multilinearEvalValue
        (deployedSuccessorPoint ConcreteProbeWitness.probePoint)
        (alignedReserveEmbed Tower
          (deployedAConversion
            (liftBaseCoins
              (yBlockOrdinary
                (polynomialBlock
                  (AspisV5ComponentARankCompletion.kernelShift
                    ConcreteProbeWitness.naturalQ18 shift.val)))))) =
      successorAQExact *
        (successorDotsExact shift - successorDotsExact 0) := by
  rw [concreteSuccessor_exact]
  rw [aligned_y_kernelShift_eval _ successorWeights shift
    successorWeights_exact]
  rw [yPrefix_pointToExact, successor_aQ_exact]
  rw [show exactDotFor successorWeights shift 0 = successorDotsExact shift by
      exact congrFun successorDots_exact shift]
  rw [show exactDotFor successorWeights 0 0 = successorDotsExact 0 by
      exact congrFun successorDots_exact 0]

private theorem xPrefix_concreteXor :
    xPrefix (deployedXor12Point ConcreteProbeWitness.probePoint) =
      baseAPExact := by
  rw [concretePoint_exact]
  change exactAPFor point = baseAPExact
  exact point_aP_exact

private theorem yPrefix_concreteXor :
    yPrefix (deployedXor12Point ConcreteProbeWitness.probePoint) =
      baseAQExact := by
  rw [concretePoint_exact]
  change exactAQFor point = baseAQExact
  exact point_aQ_exact

/-- Maintained x-block terminal value at the concrete xor-12 point. -/
theorem aligned_x_kernelShift_eval_xor (shift : Fin 12) :
    multilinearEvalValue
        (deployedXor12Point ConcreteProbeWitness.probePoint)
        (alignedReserveEmbed Tower
          (deployedAConversion
            (liftBaseCoins
              (xBlockOrdinary
                (polynomialBlock
                  (AspisV5ComponentARankCompletion.kernelShift
                    ConcreteProbeWitness.naturalQ18 shift.val)))))) =
      baseAPExact * (xorDotsExact shift - xorDotsExact 0) := by
  rw [multilinearEvalValue_xBlock_raw]
  rw [polynomialBlock_kernelShift_eq_ordinaryShift_sub_fun]
  rw [convertedNatural_sub, naturalWeightedDot_sub]
  rw [convertedNatural_maintained_shift_eq_shiftedExact,
    convertedNatural_maintained_eq_shiftedExact_zero]
  rw [naturalWeightedDot_shiftedExact_xorSix _ weights shift
    concreteXorWeights_exact]
  have hzero :
      naturalWeightedDot
          (deployedXor12Point ConcreteProbeWitness.probePoint)
          (shiftedExact 0) =
        exactDotFor weights 0 6 := by
    simpa using naturalWeightedDot_shiftedExact_xorSix
      (deployedXor12Point ConcreteProbeWitness.probePoint) weights
      (0 : Fin 12) concreteXorWeights_exact
  rw [hzero, xPrefix_concreteXor]
  rw [show exactDotFor weights shift 6 = xorDotsExact shift by
      exact congrFun xorDots_exact shift]
  rw [show exactDotFor weights 0 6 = xorDotsExact 0 by
      exact congrFun xorDots_exact 0]

/-- Maintained y-block terminal value at the concrete xor-12 point. -/
theorem aligned_y_kernelShift_eval_xor (shift : Fin 12) :
    multilinearEvalValue
        (deployedXor12Point ConcreteProbeWitness.probePoint)
        (alignedReserveEmbed Tower
          (deployedAConversion
            (liftBaseCoins
              (yBlockOrdinary
                (polynomialBlock
                  (AspisV5ComponentARankCompletion.kernelShift
                    ConcreteProbeWitness.naturalQ18 shift.val)))))) =
      baseAQExact * (xorDotsExact shift - xorDotsExact 0) := by
  rw [multilinearEvalValue_yBlock_raw]
  rw [polynomialBlock_kernelShift_eq_ordinaryShift_sub_fun]
  rw [convertedNatural_sub, naturalWeightedDot_sub]
  rw [convertedNatural_maintained_shift_eq_shiftedExact,
    convertedNatural_maintained_eq_shiftedExact_zero]
  rw [naturalWeightedDot_shiftedExact_xorSix _ weights shift
    concreteXorWeights_exact]
  have hzero :
      naturalWeightedDot
          (deployedXor12Point ConcreteProbeWitness.probePoint)
          (shiftedExact 0) =
        exactDotFor weights 0 6 := by
    simpa using naturalWeightedDot_shiftedExact_xorSix
      (deployedXor12Point ConcreteProbeWitness.probePoint) weights
      (0 : Fin 12) concreteXorWeights_exact
  rw [hzero, yPrefix_concreteXor]
  rw [show exactDotFor weights shift 6 = xorDotsExact shift by
      exact congrFun xorDots_exact shift]
  rw [show exactDotFor weights 0 6 = xorDotsExact 0 by
      exact congrFun xorDots_exact 0]

end GoodMatricesCurrent.ConcreteProbeTerminalMatrixDischarge
