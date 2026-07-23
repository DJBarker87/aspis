import GoodMatricesCurrent.ProbeTerminalMatrixAssembly
import GoodMatricesCurrent.SourceExtractedTerminalPrefixes

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedGoodAMatrixOutput

open GoodMatricesCurrent.ProbeAbstractDot
open GoodMatricesCurrent.ProbeGeneratedConcrete
open GoodMatricesCurrent.ProbeTerminalMatrix
open GoodMatricesCurrent.ProbeTerminalMatrixAssembly
open GoodMatricesCurrent.SourceExtractedTerminalEvaluator
open GoodMatricesCurrent.SourceExtractedTerminalField
open GoodMatricesCurrent.SourceExtractedTerminalPrefixes
open GoodMatricesCurrent.SourceExtractedTerminalWeights
open AspisV5GoodGateDotBatching
open AspisV5GoodGateSparseShift

abbrev ExactM31 := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev LocalQM31 :=
  GoodMatricesCurrent.SourceExtractedTerminalField.LocalQM31
abbrev LocalNatural :=
  GoodMatricesCurrent.SourceExtractedTerminalEvaluator.LocalNatural
abbrev LocalWeights :=
  GoodMatricesCurrent.SourceExtractedTerminalEvaluator.LocalWeights

@[simp] theorem exactQM31Limb_qm31ToExact
    (value : GoodMatricesCurrent.SourceExtractedTerminalField.LocalQM31)
    (limb : Fin 4) :
    exactQM31Limb (qm31ToExact value) limb =
      ((qm31Limb value limb).val : ExactM31) := by
  fin_cases limb <;> rfl

theorem deployedBatchedLimb_eq_exactDotLimbFor
    (natural : LocalNatural) (localWeights : LocalWeights)
    (shift : Fin 12) (mask limb : Nat)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights localWeights)
    (hmask : MaskBound mask) (hlimb : limb < 4)
    (hnaturalExact : naturalToExact natural = shiftedExact shift.val) :
    (deployedBatchedLimb natural localWeights shift mask limb : ExactM31) =
      exactDotLimbFor localWeights shift mask limb := by
  unfold deployedBatchedLimb
  rw [batchedDot24_cast_eq_ordinary
    (paddedLeft natural shift) (paddedWeight localWeights shift mask limb)
    (paddedLeft_canonical natural hnatural shift)
    (paddedWeight_canonical localWeights hweights shift mask limb hmask hlimb)]
  rw [← ordinaryDot24_cast]
  unfold paddedLeft paddedWeight
  rw [ordinaryDot24_zeroPad_eq_prefix _
    (deployedSupportCount_bounds shift).2]
  rw [Nat.cast_sum]
  unfold exactDotLimbFor
  apply Finset.sum_congr rfl
  intro logical hlogical
  have hlogical' : logical < deployedSupportCount shift :=
    Finset.mem_range.mp hlogical
  have hindex : deployedSupportIndex shift logical < 48 :=
    supportIndex_lt_48 shift logical hlogical'
  have hweightIndex : Nat.xor (deployedSupportIndex shift logical) mask < 64 :=
    hmask _ hindex
  rw [Nat.cast_mul]
  unfold deployedLeft deployedWeight
  rw [naturalWord_active natural _ hindex]
  rw [weightWord_active localWeights _ limb hweightIndex hlimb]
  simp only [deployedSupportIndex] at hindex hweightIndex ⊢
  rw [dif_pos hindex]
  rw [show ((naturalEntry natural
        ⟨shift.val % 2 + 2 * logical, hindex⟩).val : ExactM31) =
      shiftedExact shift.val
        ⟨shift.val % 2 + 2 * logical, hindex⟩ by
    simpa [naturalToExact] using
      congrFun hnaturalExact
        ⟨shift.val % 2 + 2 * logical, hindex⟩]
  unfold exactWeightWordFor
  rw [dif_pos hweightIndex, dif_pos hlimb]
  simp only [weightsToExact]
  rw [exactQM31Limb_qm31ToExact]

theorem deployedBatchedQM31_eq_exactDotFor
    (natural : LocalNatural) (localWeights : LocalWeights)
    (shift : Fin 12) (mask : Nat)
    (hnatural : CanonicalLocalNatural natural)
    (hweights : CanonicalLocalWeights localWeights)
    (hmask : MaskBound mask)
    (hnaturalExact : naturalToExact natural = shiftedExact shift.val) :
    deployedBatchedQM31 natural localWeights shift mask =
      exactDotFor localWeights shift mask := by
  ext <;> simp only [deployedBatchedQM31, exactDotFor, exactQ]
  · exact deployedBatchedLimb_eq_exactDotLimbFor natural localWeights shift
      mask 0 hnatural hweights hmask (by omega) hnaturalExact
  · exact deployedBatchedLimb_eq_exactDotLimbFor natural localWeights shift
      mask 1 hnatural hweights hmask (by omega) hnaturalExact
  · exact deployedBatchedLimb_eq_exactDotLimbFor natural localWeights shift
      mask 2 hnatural hweights hmask (by omega) hnaturalExact
  · exact deployedBatchedLimb_eq_exactDotLimbFor natural localWeights shift
      mask 3 hnatural hweights hmask (by omega) hnaturalExact

theorem kernel_canonical :
    GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalKernel
      kernel := by
  intro index
  fin_cases index <;>
    norm_num [kernel, Aeneas.Std.Array.make,
      GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalM31,
      AspisV5ComponentCQM31TowerExact.P]

def ConcreteShiftedDirections
    (directions : alloc.vec.Vec LocalNatural) : Prop :=
  directions.val.length = 12 ∧
  ∀ shift : Fin 12,
    ∃ natural : LocalNatural,
      directions.val[shift.val]? = some natural ∧
      CanonicalLocalNatural natural ∧
      naturalToExact natural = shiftedExact shift.val

theorem concrete_good_shifted_directions_spec :
    ∃ directions : alloc.vec.Vec LocalNatural,
      v5_cu_probe.good_gate_probe.good_shifted_directions kernel =
        .ok directions ∧
      ConcreteShiftedDirections directions := by
  letI : NeZero (2 : ExactM31) := ⟨by decide⟩
  obtain ⟨directions, hcall, hlength, hentries⟩ :=
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.good_shifted_directions_exact_spec
      kernel kernel_canonical
  refine ⟨directions, hcall, hlength, ?_⟩
  intro shift
  obtain ⟨natural, hlookup, hcanonical, hexact⟩ := hentries shift
  refine ⟨natural, hlookup, hcanonical, ?_⟩
  change GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact natural =
    shiftedExact shift.val
  calc
    GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact natural =
        convert (ordinaryShiftIter shift.val
          (GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary
            kernel)) := hexact
    _ = sparseShiftIter shift.val
          (convert
            (GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary
              kernel)) :=
      (AspisV5GoodGateSparseShift.goodA_complete_shift_chain
        (GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary kernel)
        (GoodMatricesCurrent.SourceExtractedGoodAModelBridge.evenKernelOrdinary_supportedBelow
          kernel) shift.val (by omega)).symm
    _ = sparseShiftIter shift.val
          (GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
            baseDirection) := by
      have hbaseExact :
          GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
              baseDirection =
            convert
              (GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary
                kernel) :=
        baseDirection_source_exact.trans
          (GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion_eq_convert
            kernel)
      rw [hbaseExact]
    _ = shiftedExact shift.val := rfl

abbrev LocalDots := Array LocalQM31 12#usize

def dotEntry (dots : LocalDots) (index : Fin 12) : LocalQM31 :=
  dots.val[index.val]'(by rw [dots.property]; exact index.isLt)

def DotsPrefixExact (dots : LocalDots) (expected : Fin 12 → ExactQM31)
    (count : Nat) : Prop :=
  ∀ index : Fin 12, index.val < count →
    CanonicalLocalQM31 (dotEntry dots index) ∧
    qm31ToExact (dotEntry dots index) = expected index

theorem dots_index_call (dots : LocalDots) (index : Std.Usize)
    (hindex : index.val < 12) :
    Array.index_usize dots index =
      .ok (dotEntry dots ⟨index.val, hindex⟩) := by
  exact Array.index_usize_eq_ok_of_getElem_eq dots index
    (by rw [dots.property]; exact hindex) _ rfl

theorem dots_update_call (dots : LocalDots) (index : Std.Usize)
    (hindex : index.val < 12) (value : LocalQM31) :
    Array.update dots index value = .ok (dots.set index value) := by
  exact Array.update_eq_ok dots index value
    (by rw [dots.property]; exact hindex)

@[simp] theorem dotEntry_set_same (dots : LocalDots) (index : Std.Usize)
    (hindex : index.val < 12) (value : LocalQM31) :
    dotEntry (dots.set index value) ⟨index.val, hindex⟩ = value := by
  unfold dotEntry
  exact List.getElem_set_self (by
    simp only [List.length_set]
    rw [dots.property]
    exact hindex)

@[simp] theorem dotEntry_set_other (dots : LocalDots) (index : Std.Usize)
    (value : LocalQM31) (output : Fin 12)
    (hne : index.val ≠ output.val) :
    dotEntry (dots.set index value) output = dotEntry dots output := by
  unfold dotEntry
  exact List.getElem_set_ne hne (by
    simp only [List.length_set]
    rw [dots.property]
    exact output.isLt)

theorem dotsPrefixExact_set_next (dots : LocalDots)
    (expected : Fin 12 → ExactQM31) (runtimeIndex : Std.Usize)
    (index : Fin 12) (value : LocalQM31)
    (hruntimeIndex : runtimeIndex.val = index.val)
    (hprefix : DotsPrefixExact dots expected index.val)
    (hcanonical : CanonicalLocalQM31 value)
    (hexact : qm31ToExact value = expected index) :
    DotsPrefixExact (dots.set runtimeIndex value) expected (index.val + 1) := by
  intro output houtput
  by_cases heq : output.val = index.val
  · have houtputEq : output = index := Fin.ext heq
    subst output
    have hbound : runtimeIndex.val < 12 := by
      rw [hruntimeIndex]
      exact index.isLt
    have hentry :
        dotEntry (dots.set runtimeIndex value)
          ⟨runtimeIndex.val, hbound⟩ = value :=
      dotEntry_set_same dots runtimeIndex hbound value
    have hfin : (⟨runtimeIndex.val, hbound⟩ : Fin 12) = index := by
      apply Fin.ext
      exact hruntimeIndex
    rw [hfin] at hentry
    rw [hentry]
    exact ⟨hcanonical, hexact⟩
  · have hold : output.val < index.val := by omega
    have hprevious := hprefix output hold
    have hne : runtimeIndex.val ≠ output.val := by
      rw [hruntimeIndex]
      exact Ne.symm heq
    rw [dotEntry_set_other dots runtimeIndex value output hne]
    exact hprevious

theorem xor_suffix_mask_call :
    v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals.XOR12_SUFFIX_MASK =
      .ok 6#usize := by
  have hshiftTwo : (1#usize <<< 2#i32) = (.ok 4#usize) := by
    have htoNat : (2#i32).toNat = 2 := by
      rfl
    change UScalar.shiftLeft_IScalar 1#usize 2#i32 = .ok 4#usize
    unfold UScalar.shiftLeft_IScalar
    rw [if_pos (by norm_num)]
    unfold UScalar.shiftLeft
    rw [if_pos (by
      rcases System.Platform.numBits_eq with hp | hp <;> norm_num [hp])]
    rw [htoNat]
    congr 2
    apply BitVec.toNat_injective
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [hp, IScalar.toNat, BitVec.toNat_shiftLeft,
        Nat.shiftLeft_eq, Int.toNat_of_nonneg]
  have hshiftOne : (1#usize <<< 1#i32) = (.ok 2#usize) := by
    change UScalar.shiftLeft_IScalar 1#usize 1#i32 = .ok 2#usize
    unfold UScalar.shiftLeft_IScalar
    rw [if_pos (by norm_num)]
    unfold UScalar.shiftLeft
    rw [if_pos (by
      rcases System.Platform.numBits_eq with hp | hp <;> norm_num [hp])]
    congr 2
    apply BitVec.toNat_injective
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [hp, IScalar.toNat, BitVec.toNat_shiftLeft,
        Nat.shiftLeft_eq]
  unfold
    v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals.XOR12_SUFFIX_MASK
  rw [hshiftTwo]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hshiftOne]
  rfl

def ConcreteShiftedSlice (directions : Slice LocalNatural) : Prop :=
  directions.val.length = 12 ∧
  ∀ shift : Fin 12,
    ∃ natural : LocalNatural,
      directions.val[shift.val]? = some natural ∧
      CanonicalLocalNatural natural ∧
      naturalToExact natural = shiftedExact shift.val

theorem concreteShiftedSlice_deref
    (directions : alloc.vec.Vec LocalNatural)
    (hdirections : ConcreteShiftedDirections directions) :
    ConcreteShiftedSlice (alloc.vec.Vec.deref directions) := by
  exact hdirections

theorem shifted_slice_index_call (directions : Slice LocalNatural)
    (runtimeShift : Std.Usize) (shift : Fin 12) (natural : LocalNatural)
    (hruntimeShift : runtimeShift.val = shift.val)
    (hlookup : directions.val[shift.val]? = some natural) :
    Slice.index_usize directions runtimeShift = .ok natural := by
  unfold Slice.index_usize
  have hlookupRuntime :
      directions.val[runtimeShift.val]? = some natural := by
    simpa [hruntimeShift] using hlookup
  rw [Slice.getElem?_Usize_eq, hlookupRuntime]

def BaseXorLoopInvariant (baseDots xorDots : LocalDots)
    (runtimeShift : Std.Usize) : Prop :=
  runtimeShift.val ≤ 12 ∧
  DotsPrefixExact baseDots
      (fun shift => exactDotFor weights shift 0) runtimeShift.val ∧
  DotsPrefixExact xorDots
      (fun shift => exactDotFor weights shift 6) runtimeShift.val

abbrev baseXorBody :=
  v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals_loop.body

abbrev baseXorLoop :=
  v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals_loop

theorem baseXorBody_step (directions : Slice LocalNatural)
    (hdirections : ConcreteShiftedSlice directions)
    (baseDots xorDots : LocalDots) (runtimeShift : Std.Usize)
    (hinvariant : BaseXorLoopInvariant baseDots xorDots runtimeShift)
    (hcontinue : runtimeShift.val < 12) :
    ∃ nextBase nextXor : LocalDots, ∃ nextShift : Std.Usize,
      baseXorBody directions weights baseDots xorDots runtimeShift =
        .ok (.cont (nextBase, nextXor, nextShift)) ∧
      nextShift.val = runtimeShift.val + 1 ∧
      BaseXorLoopInvariant nextBase nextXor nextShift := by
  let shift : Fin 12 := ⟨runtimeShift.val, hcontinue⟩
  obtain ⟨natural, hlookup, hnatural, hnaturalExact⟩ :=
    hdirections.2 shift
  have hnaturalCall :
      Slice.index_usize directions runtimeShift = .ok natural :=
    shifted_slice_index_call directions runtimeShift shift natural rfl hlookup
  obtain ⟨baseResult, xorResult, hevaluate, hbaseCanonical,
      hxorCanonical, hbaseExact, hxorExact⟩ :=
    evaluate_shifted_in_aligned_block_base_xor_exact_spec
      natural weights runtimeShift 6#usize shift 6 rfl rfl
      hnatural weights_canonical mask_six_bound
  have hbaseExact' :
      qm31ToExact baseResult = exactDotFor weights shift 0 := by
    rw [hbaseExact,
      deployedBatchedQM31_eq_exactDotFor natural weights shift 0 hnatural
        weights_canonical mask_zero_bound hnaturalExact]
  have hxorExact' :
      qm31ToExact xorResult = exactDotFor weights shift 6 := by
    rw [hxorExact,
      deployedBatchedQM31_eq_exactDotFor natural weights shift 6 hnatural
        weights_canonical mask_six_bound hnaturalExact]
  let nextBase := baseDots.set runtimeShift baseResult
  let nextXor := xorDots.set runtimeShift xorResult
  let nextShift := Std.Usize.wrapping_add runtimeShift 1#usize
  have hnextShift : nextShift.val = runtimeShift.val + 1 := by
    unfold nextShift
    rw [Std.Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits, hp] <;>
      omega
  have hbaseUpdate :
      Array.update baseDots runtimeShift baseResult = .ok nextBase := by
    simpa [nextBase] using
      dots_update_call baseDots runtimeShift hcontinue baseResult
  have hxorUpdate :
      Array.update xorDots runtimeShift xorResult = .ok nextXor := by
    simpa [nextXor] using
      dots_update_call xorDots runtimeShift hcontinue xorResult
  have hbaseNext : DotsPrefixExact nextBase
      (fun next => exactDotFor weights next 0) (shift.val + 1) := by
    exact dotsPrefixExact_set_next baseDots _ runtimeShift shift baseResult rfl
      hinvariant.2.1 hbaseCanonical hbaseExact'
  have hxorNext : DotsPrefixExact nextXor
      (fun next => exactDotFor weights next 6) (shift.val + 1) := by
    exact dotsPrefixExact_set_next xorDots _ runtimeShift shift xorResult rfl
      hinvariant.2.2 hxorCanonical hxorExact'
  refine ⟨nextBase, nextXor, nextShift, ?_, hnextShift, ?_⟩
  · unfold baseXorBody
    unfold
      v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals_loop.body
    have hcondition :
        runtimeShift < v5_cu_probe.good_gate_probe.GOOD_A_SIZE := by
      apply (UScalar.lt_equiv _ _).2
      simpa [v5_cu_probe.good_gate_probe.GOOD_A_SIZE] using hcontinue
    rw [if_pos hcondition]
    rw [hnaturalCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [xor_suffix_mask_call]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hevaluate]
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let q ← Array.index_usize
        (Array.make 2#usize [baseResult, xorResult]) 0#usize
      let a1 ← Array.update baseDots runtimeShift q
      let q1 ← Array.index_usize
        (Array.make 2#usize [baseResult, xorResult]) 1#usize
      let a2 ← Array.update xorDots runtimeShift q1
      let shift1 ← lift (Std.Usize.wrapping_add runtimeShift 1#usize)
      ok (cont (a1, a2, shift1))) = _
    norm_num [Aeneas.Std.Array.index_usize, Aeneas.Std.Array.make]
    rw [hbaseUpdate]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hxorUpdate]
    rfl
  · refine ⟨?_, ?_, ?_⟩
    · rw [hnextShift]
      omega
    · simpa [hnextShift] using hbaseNext
    · simpa [hnextShift] using hxorNext

theorem baseXorLoop_spec (directions : Slice LocalNatural)
    (hdirections : ConcreteShiftedSlice directions)
    (baseDots xorDots : LocalDots) (runtimeShift : Std.Usize)
    (hinvariant : BaseXorLoopInvariant baseDots xorDots runtimeShift) :
    ∃ finalBase finalXor : LocalDots,
      baseXorLoop directions weights baseDots xorDots runtimeShift =
        .ok (finalBase, finalXor) ∧
      DotsPrefixExact finalBase
        (fun shift => exactDotFor weights shift 0) 12 ∧
      DotsPrefixExact finalXor
        (fun shift => exactDotFor weights shift 6) 12 := by
  by_cases hcontinue : runtimeShift.val < 12
  · obtain ⟨nextBase, nextXor, nextShift, hbody, hnextShift,
      hnextInvariant⟩ :=
      baseXorBody_step directions hdirections baseDots xorDots runtimeShift
        hinvariant hcontinue
    obtain ⟨finalBase, finalXor, hloop, hbase, hxor⟩ :=
      baseXorLoop_spec directions hdirections nextBase nextXor nextShift
        hnextInvariant
    refine ⟨finalBase, finalXor, ?_, hbase, hxor⟩
    change
      v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals_loop.body
          directions weights baseDots xorDots runtimeShift =
        .ok (.cont (nextBase, nextXor, nextShift)) at hbody
    unfold baseXorLoop
    unfold
      v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals_loop
    rw [loop.eq_def]
    simp only
    rw [hbody]
    exact hloop
  · have hfinal : runtimeShift.val = 12 := by
      have hupper := hinvariant.1
      omega
    have hcondition :
        ¬ runtimeShift < v5_cu_probe.good_gate_probe.GOOD_A_SIZE := by
      intro hlt
      apply hcontinue
      have := (UScalar.lt_equiv _ _).1 hlt
      simpa [v5_cu_probe.good_gate_probe.GOOD_A_SIZE] using this
    have hbody : baseXorBody directions weights baseDots xorDots runtimeShift =
        .ok (.done (baseDots, xorDots)) := by
      unfold baseXorBody
      unfold
        v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals_loop.body
      rw [if_neg hcondition]
    refine ⟨baseDots, xorDots, ?_, ?_, ?_⟩
    · change
        v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals_loop.body
            directions weights baseDots xorDots runtimeShift =
          .ok (.done (baseDots, xorDots)) at hbody
      unfold baseXorLoop
      unfold
        v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals_loop
      rw [loop.eq_def]
      simp only
      rw [hbody]
    · simpa [hfinal] using hinvariant.2.1
    · simpa [hfinal] using hinvariant.2.2
termination_by 12 - runtimeShift.val
decreasing_by
  rw [hnextShift]
  omega

def SuccessorLoopInvariant (dots : LocalDots)
    (runtimeShift : Std.Usize) : Prop :=
  runtimeShift.val ≤ 12 ∧
  DotsPrefixExact dots
    (fun shift => exactDotFor successorWeights shift 0) runtimeShift.val

abbrev successorBody :=
  v5_cu_probe.good_gate_probe.fill_good_successor_terminal_loop.body

abbrev successorLoop :=
  v5_cu_probe.good_gate_probe.fill_good_successor_terminal_loop

theorem successorBody_step (directions : Slice LocalNatural)
    (hdirections : ConcreteShiftedSlice directions)
    (dots : LocalDots) (runtimeShift : Std.Usize)
    (hinvariant : SuccessorLoopInvariant dots runtimeShift)
    (hcontinue : runtimeShift.val < 12) :
    ∃ nextDots : LocalDots, ∃ nextShift : Std.Usize,
      successorBody directions successorWeights dots runtimeShift =
        .ok (.cont (nextDots, nextShift)) ∧
      nextShift.val = runtimeShift.val + 1 ∧
      SuccessorLoopInvariant nextDots nextShift := by
  let shift : Fin 12 := ⟨runtimeShift.val, hcontinue⟩
  obtain ⟨natural, hlookup, hnatural, hnaturalExact⟩ :=
    hdirections.2 shift
  have hnaturalCall :
      Slice.index_usize directions runtimeShift = .ok natural :=
    shifted_slice_index_call directions runtimeShift shift natural rfl hlookup
  obtain ⟨result, hevaluate, hcanonical, hexact⟩ :=
    evaluate_shifted_in_aligned_block_exact_spec natural successorWeights
      runtimeShift 0#usize shift 0 rfl rfl hnatural
      successorWeights_canonical mask_zero_bound
  have hexact' :
      qm31ToExact result = exactDotFor successorWeights shift 0 := by
    rw [hexact,
      deployedBatchedQM31_eq_exactDotFor natural successorWeights shift 0
        hnatural successorWeights_canonical mask_zero_bound hnaturalExact]
  let nextDots := dots.set runtimeShift result
  let nextShift := Std.Usize.wrapping_add runtimeShift 1#usize
  have hnextShift : nextShift.val = runtimeShift.val + 1 := by
    unfold nextShift
    rw [Std.Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits, hp] <;>
      omega
  have hupdate : Array.update dots runtimeShift result = .ok nextDots := by
    simpa [nextDots] using
      dots_update_call dots runtimeShift hcontinue result
  have hnextPrefix : DotsPrefixExact nextDots
      (fun next => exactDotFor successorWeights next 0) (shift.val + 1) := by
    exact dotsPrefixExact_set_next dots _ runtimeShift shift result rfl
      hinvariant.2 hcanonical hexact'
  refine ⟨nextDots, nextShift, ?_, hnextShift, ?_⟩
  · unfold successorBody
    unfold v5_cu_probe.good_gate_probe.fill_good_successor_terminal_loop.body
    have hcondition :
        runtimeShift < v5_cu_probe.good_gate_probe.GOOD_A_SIZE := by
      apply (UScalar.lt_equiv _ _).2
      simpa [v5_cu_probe.good_gate_probe.GOOD_A_SIZE] using hcontinue
    rw [if_pos hcondition, hnaturalCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hevaluate]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hupdate]
    rfl
  · constructor
    · rw [hnextShift]
      omega
    · simpa [hnextShift] using hnextPrefix

theorem successorLoop_spec (directions : Slice LocalNatural)
    (hdirections : ConcreteShiftedSlice directions)
    (dots : LocalDots) (runtimeShift : Std.Usize)
    (hinvariant : SuccessorLoopInvariant dots runtimeShift) :
    ∃ finalDots : LocalDots,
      successorLoop directions successorWeights dots runtimeShift =
        .ok finalDots ∧
      DotsPrefixExact finalDots
        (fun shift => exactDotFor successorWeights shift 0) 12 := by
  by_cases hcontinue : runtimeShift.val < 12
  · obtain ⟨nextDots, nextShift, hbody, hnextShift, hnextInvariant⟩ :=
      successorBody_step directions hdirections dots runtimeShift
        hinvariant hcontinue
    obtain ⟨finalDots, hloop, hfinal⟩ :=
      successorLoop_spec directions hdirections nextDots nextShift
        hnextInvariant
    refine ⟨finalDots, ?_, hfinal⟩
    change
      v5_cu_probe.good_gate_probe.fill_good_successor_terminal_loop.body
          directions successorWeights dots runtimeShift =
        .ok (.cont (nextDots, nextShift)) at hbody
    unfold successorLoop
    unfold v5_cu_probe.good_gate_probe.fill_good_successor_terminal_loop
    rw [loop.eq_def]
    simp only
    rw [hbody]
    exact hloop
  · have hfinalShift : runtimeShift.val = 12 := by
      have hupper := hinvariant.1
      omega
    have hcondition :
        ¬ runtimeShift < v5_cu_probe.good_gate_probe.GOOD_A_SIZE := by
      intro hlt
      apply hcontinue
      have := (UScalar.lt_equiv _ _).1 hlt
      simpa [v5_cu_probe.good_gate_probe.GOOD_A_SIZE] using this
    have hbody : successorBody directions successorWeights dots runtimeShift =
        .ok (.done dots) := by
      unfold successorBody
      unfold
        v5_cu_probe.good_gate_probe.fill_good_successor_terminal_loop.body
      rw [if_neg hcondition]
    refine ⟨dots, ?_, ?_⟩
    · change
        v5_cu_probe.good_gate_probe.fill_good_successor_terminal_loop.body
            directions successorWeights dots runtimeShift =
          .ok (.done dots) at hbody
      unfold successorLoop
      unfold v5_cu_probe.good_gate_probe.fill_good_successor_terminal_loop
      rw [loop.eq_def]
      simp only
      rw [hbody]
    · simpa [hfinalShift] using hinvariant.2
termination_by 12 - runtimeShift.val
decreasing_by
  rw [hnextShift]
  omega

abbrev LocalRow := Array
  GoodMatricesCurrent.SourceExtractedTerminalField.LocalM31 12#usize
abbrev LocalAMatrix := Array LocalRow 12#usize
abbrev LocalLimbs := Array
  GoodMatricesCurrent.SourceExtractedTerminalField.LocalM31 4#usize

def matrixRowEntry (matrix : LocalAMatrix) (row : Fin 12) : LocalRow :=
  matrix.val[row.val]'(by rw [matrix.property]; exact row.isLt)

def matrixEntry (matrix : LocalAMatrix) (row column : Fin 12) :
    GoodMatricesCurrent.SourceExtractedTerminalField.LocalM31 :=
  (matrixRowEntry matrix row)[column.val]!

def limbEntry (limbs : LocalLimbs) (limb : Fin 4) :
    GoodMatricesCurrent.SourceExtractedTerminalField.LocalM31 :=
  limbs.val[limb.val]'(by rw [limbs.property]; exact limb.isLt)

@[simp] theorem matrixRowEntry_set_same (matrix : LocalAMatrix)
    (row : Std.Usize) (hrow : row.val < 12) (value : LocalRow) :
    matrixRowEntry (matrix.set row value) ⟨row.val, hrow⟩ = value := by
  unfold matrixRowEntry
  exact List.getElem_set_self (by
    simp only [List.length_set]
    rw [matrix.property]
    exact hrow)

@[simp] theorem matrixRowEntry_set_other (matrix : LocalAMatrix)
    (row : Std.Usize) (value : LocalRow) (output : Fin 12)
    (hne : row.val ≠ output.val) :
    matrixRowEntry (matrix.set row value) output =
      matrixRowEntry matrix output := by
  unfold matrixRowEntry
  exact List.getElem_set_ne hne (by
    simp only [List.length_set]
    rw [matrix.property]
    exact output.isLt)

@[simp] theorem rowEntry_set_same (rowValues : LocalRow)
    (column : Std.Usize) (hcolumn : column.val < 12)
    (value : GoodMatricesCurrent.SourceExtractedTerminalField.LocalM31) :
    (rowValues.set column value)[column.val]! = value := by
  apply Array.getElem!_Nat_set_eq
  constructor
  · rfl
  · simpa [Array.length] using hcolumn

@[simp] theorem rowEntry_set_other (rowValues : LocalRow)
    (column : Std.Usize)
    (value : GoodMatricesCurrent.SourceExtractedTerminalField.LocalM31)
    (output : Fin 12) (hne : column.val ≠ output.val) :
    (rowValues.set column value)[output.val]! =
      rowValues[output.val]! := by
  exact Array.getElem!_Nat_set_ne rowValues column output.val value hne

theorem matrixEntry_set_cell (matrix : LocalAMatrix)
    (runtimeRow runtimeColumn : Std.Usize)
    (hrow : runtimeRow.val < 12) (hcolumn : runtimeColumn.val < 12)
    (value : GoodMatricesCurrent.SourceExtractedTerminalField.LocalM31)
    (outputRow outputColumn : Fin 12) :
    matrixEntry
        (matrix.set runtimeRow
          ((matrixRowEntry matrix ⟨runtimeRow.val, hrow⟩).set
            runtimeColumn value)) outputRow outputColumn =
      if runtimeRow.val = outputRow.val then
        if runtimeColumn.val = outputColumn.val then value
        else matrixEntry matrix outputRow outputColumn
      else matrixEntry matrix outputRow outputColumn := by
  by_cases hrowEq : runtimeRow.val = outputRow.val
  · rw [if_pos hrowEq]
    have hfinRow : (⟨runtimeRow.val, hrow⟩ : Fin 12) = outputRow :=
      Fin.ext hrowEq
    subst outputRow
    unfold matrixEntry
    rw [matrixRowEntry_set_same]
    by_cases hcolumnEq : runtimeColumn.val = outputColumn.val
    · rw [if_pos hcolumnEq]
      apply Array.getElem!_Nat_set_eq
      constructor
      · exact hcolumnEq
      · simpa [Array.length] using outputColumn.isLt
    · rw [if_neg hcolumnEq]
      exact rowEntry_set_other _ _ _ _ hcolumnEq
  · rw [if_neg hrowEq]
    unfold matrixEntry
    rw [matrixRowEntry_set_other _ _ _ _ hrowEq]

def WriteLimbPrefix (before current : LocalAMatrix)
    (terminal direction count : Nat) (limbs : LocalLimbs) : Prop :=
  ∀ row column : Fin 12,
    matrixEntry current row column =
      if column.val = direction ∧
          4 * terminal ≤ row.val ∧ row.val < 4 * terminal + count then
        limbEntry limbs
          ⟨(row.val - 4 * terminal) % 4, Nat.mod_lt _ (by omega)⟩
      else matrixEntry before row column

theorem limbs_index_call (limbs : LocalLimbs) (runtimeLimb : Std.Usize)
    (hlimb : runtimeLimb.val < 4) :
    Array.index_usize limbs runtimeLimb =
      .ok (limbEntry limbs ⟨runtimeLimb.val, hlimb⟩) := by
  exact Array.index_usize_eq_ok_of_getElem_eq limbs runtimeLimb
    (by rw [limbs.property]; exact hlimb) _ rfl

theorem matrix_index_mut_call (matrix : LocalAMatrix)
    (runtimeRow : Std.Usize) (hrow : runtimeRow.val < 12) :
    Array.index_mut_usize matrix runtimeRow =
      .ok (matrixRowEntry matrix ⟨runtimeRow.val, hrow⟩,
        matrix.set runtimeRow) := by
  unfold Array.index_mut_usize
  have hcall := Array.index_usize_eq_ok_of_getElem_eq matrix runtimeRow
    (by rw [matrix.property]; exact hrow)
    (matrixRowEntry matrix ⟨runtimeRow.val, hrow⟩)
    (by rfl)
  rw [hcall]
  simp only [Aeneas.Std.bind_tc_ok]

theorem row_update_call (rowValues : LocalRow)
    (runtimeColumn : Std.Usize) (hcolumn : runtimeColumn.val < 12)
    (value : GoodMatricesCurrent.SourceExtractedTerminalField.LocalM31) :
    Array.update rowValues runtimeColumn value =
      .ok (rowValues.set runtimeColumn value) := by
  exact Array.update_eq_ok rowValues runtimeColumn value
    (by rw [rowValues.property]; exact hcolumn)

abbrev writeLimbBody :=
  v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0_loop0.body

abbrev writeLimbLoop :=
  v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0_loop0

theorem writeLimbBody_step (before current : LocalAMatrix)
    (runtimeTerminal runtimeDirection : Std.Usize)
    (terminal : Fin 3) (direction : Fin 12)
    (hruntimeTerminal : runtimeTerminal.val = terminal.val)
    (hruntimeDirection : runtimeDirection.val = direction.val)
    (limbs : LocalLimbs) (runtimeLimb : Std.Usize)
    (hlimbBound : runtimeLimb.val ≤ 4)
    (hinvariant : WriteLimbPrefix before current terminal.val direction.val
      runtimeLimb.val limbs)
    (hcontinue : runtimeLimb.val < 4) :
    ∃ nextMatrix : LocalAMatrix, ∃ nextLimb : Std.Usize,
      writeLimbBody runtimeTerminal runtimeDirection limbs current runtimeLimb =
        .ok (.cont (nextMatrix, nextLimb)) ∧
      nextLimb.val = runtimeLimb.val + 1 ∧
      WriteLimbPrefix before nextMatrix terminal.val direction.val
        nextLimb.val limbs := by
  let limb : Fin 4 := ⟨runtimeLimb.val, hcontinue⟩
  let runtimeBaseRow := Std.Usize.wrapping_mul 4#usize runtimeTerminal
  have hbaseRow : runtimeBaseRow.val = 4 * terminal.val := by
    unfold runtimeBaseRow
    rw [Std.Usize.wrapping_mul_val_eq, hruntimeTerminal]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits, hp] <;>
      omega
  let runtimeRow := Std.Usize.wrapping_add runtimeBaseRow runtimeLimb
  have hrow : runtimeRow.val = 4 * terminal.val + runtimeLimb.val := by
    unfold runtimeRow
    rw [Std.Usize.wrapping_add_val_eq, hbaseRow]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits, hp] <;>
      omega
  have hrowBound : runtimeRow.val < 12 := by
    rw [hrow]
    have := terminal.isLt
    omega
  let value := limbEntry limbs limb
  let nextRow :=
    (matrixRowEntry current ⟨runtimeRow.val, hrowBound⟩).set
      runtimeDirection value
  let nextMatrix := current.set runtimeRow nextRow
  let nextLimb := Std.Usize.wrapping_add runtimeLimb 1#usize
  have hnextLimb : nextLimb.val = runtimeLimb.val + 1 := by
    unfold nextLimb
    rw [Std.Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits, hp] <;>
      omega
  have hlimbCall : Array.index_usize limbs runtimeLimb = .ok value := by
    simpa [value, limb] using limbs_index_call limbs runtimeLimb hcontinue
  have hmatrixCall : Array.index_mut_usize current runtimeRow =
      .ok (matrixRowEntry current ⟨runtimeRow.val, hrowBound⟩,
        current.set runtimeRow) :=
    matrix_index_mut_call current runtimeRow hrowBound
  have hrowUpdate : Array.update
      (matrixRowEntry current ⟨runtimeRow.val, hrowBound⟩)
      runtimeDirection value = .ok nextRow := by
    simpa [nextRow] using row_update_call
      (matrixRowEntry current ⟨runtimeRow.val, hrowBound⟩)
      runtimeDirection (by simpa [hruntimeDirection] using direction.isLt) value
  refine ⟨nextMatrix, nextLimb, ?_, hnextLimb, ?_⟩
  · unfold writeLimbBody
    unfold
      v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0_loop0.body
    have hcondition : runtimeLimb < (Array.to_slice limbs).len := by
      apply (UScalar.lt_equiv _ _).2
      simpa [Array.to_slice, Slice.len, limbs.property] using hcontinue
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
    rw [if_pos hcondition, hlimbCall]
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let i1 ← lift (Std.Usize.wrapping_mul 4#usize runtimeTerminal)
      let i2 ← lift (Std.Usize.wrapping_add i1 runtimeLimb)
      let (a, index_mut_back) ← Array.index_mut_usize current i2
      let a1 ← Array.update a runtimeDirection value
      let limb1 ← lift (Std.Usize.wrapping_add runtimeLimb 1#usize)
      let a2 := index_mut_back a1
      ok (cont (a2, limb1))) = _
    change (do
      let (a, index_mut_back) ← Array.index_mut_usize current runtimeRow
      let a1 ← Array.update a runtimeDirection value
      let limb1 ← lift (Std.Usize.wrapping_add runtimeLimb 1#usize)
      let a2 := index_mut_back a1
      ok (cont (a2, limb1))) = _
    rw [hmatrixCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hrowUpdate]
    rfl
  · intro outputRow outputColumn
    rw [hnextLimb]
    rw [matrixEntry_set_cell current runtimeRow runtimeDirection hrowBound
      (by simpa [hruntimeDirection] using direction.isLt) value]
    by_cases hnewRow : runtimeRow.val = outputRow.val
    · rw [if_pos hnewRow]
      by_cases hnewColumn : runtimeDirection.val = outputColumn.val
      · rw [if_pos hnewColumn]
        rw [hrow] at hnewRow
        have hcolumn : outputColumn.val = direction.val := by
          omega
        rw [if_pos (by constructor <;> omega)]
        unfold value limbEntry limb
        congr 2
        apply Fin.ext
        simp only [Fin.val_mk]
        have hterminal := terminal.isLt
        omega
      · rw [if_neg hnewColumn]
        rw [hinvariant]
        by_cases hold : outputColumn.val = direction.val ∧
            4 * terminal.val ≤ outputRow.val ∧
              outputRow.val < 4 * terminal.val + runtimeLimb.val
        · rw [if_pos hold, if_pos (by
            constructor
            · exact hold.1
            · constructor
              · exact hold.2.1
              · omega)]
        · rw [if_neg hold]
          rw [if_neg]
          intro hactive
          apply hnewColumn
          omega
    · rw [if_neg hnewRow]
      rw [hinvariant]
      by_cases hold : outputColumn.val = direction.val ∧
          4 * terminal.val ≤ outputRow.val ∧
            outputRow.val < 4 * terminal.val + runtimeLimb.val
      · rw [if_pos hold, if_pos (by
          constructor
          · exact hold.1
          · constructor
            · exact hold.2.1
            · omega)]
      · rw [if_neg hold]
        rw [if_neg]
        intro hactive
        apply hnewRow
        rw [hrow]
        omega

theorem writeLimbLoop_spec (before current : LocalAMatrix)
    (runtimeTerminal runtimeDirection : Std.Usize)
    (terminal : Fin 3) (direction : Fin 12)
    (hruntimeTerminal : runtimeTerminal.val = terminal.val)
    (hruntimeDirection : runtimeDirection.val = direction.val)
    (limbs : LocalLimbs) (runtimeLimb : Std.Usize)
    (hlimbBound : runtimeLimb.val ≤ 4)
    (hinvariant : WriteLimbPrefix before current terminal.val direction.val
      runtimeLimb.val limbs) :
    ∃ finalMatrix : LocalAMatrix,
      writeLimbLoop current runtimeTerminal runtimeDirection limbs runtimeLimb =
        .ok finalMatrix ∧
      WriteLimbPrefix before finalMatrix terminal.val direction.val 4 limbs := by
  by_cases hcontinue : runtimeLimb.val < 4
  · obtain ⟨nextMatrix, nextLimb, hbody, hnextLimb, hnextInvariant⟩ :=
      writeLimbBody_step before current runtimeTerminal runtimeDirection
        terminal direction hruntimeTerminal hruntimeDirection limbs runtimeLimb
        hlimbBound hinvariant hcontinue
    obtain ⟨finalMatrix, hloop, hfinal⟩ :=
      writeLimbLoop_spec before nextMatrix runtimeTerminal runtimeDirection
        terminal direction hruntimeTerminal hruntimeDirection limbs nextLimb
        (by rw [hnextLimb]; omega) hnextInvariant
    refine ⟨finalMatrix, ?_, hfinal⟩
    change
      v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0_loop0.body
          runtimeTerminal runtimeDirection limbs current runtimeLimb =
        .ok (.cont (nextMatrix, nextLimb)) at hbody
    unfold writeLimbLoop
    unfold
      v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0_loop0
    rw [loop.eq_def]
    simp only
    rw [hbody]
    exact hloop
  · have hfinalLimb : runtimeLimb.val = 4 := by omega
    have hbody : writeLimbBody runtimeTerminal runtimeDirection limbs current
        runtimeLimb = .ok (.done current) := by
      unfold writeLimbBody
      unfold
        v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0_loop0.body
      simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
      have hcondition : ¬runtimeLimb < (Array.to_slice limbs).len := by
        intro hlt
        apply hcontinue
        have := (UScalar.lt_equiv _ _).1 hlt
        simpa [Array.to_slice, Slice.len, limbs.property] using this
      rw [if_neg hcondition]
    refine ⟨current, ?_, ?_⟩
    · change
        v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0_loop0.body
            runtimeTerminal runtimeDirection limbs current runtimeLimb =
          .ok (.done current) at hbody
      unfold writeLimbLoop
      unfold
        v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0_loop0
      rw [loop.eq_def]
      simp only
      rw [hbody]
    · simpa [hfinalLimb] using hinvariant
termination_by 4 - runtimeLimb.val
decreasing_by
  rw [hnextLimb]
  omega

def localQM31Limbs (value : LocalQM31) : LocalLimbs :=
  Array.make 4#usize [value.c0.a, value.c0.b, value.c1.a, value.c1.b]

theorem m31_coordinates_call (value : LocalQM31) :
    v5_cu_probe.good_gate_probe.m31_coordinates value =
      .ok (localQM31Limbs value) := by
  rfl

theorem localQM31Limbs_exact (value : LocalQM31) (limb : Fin 4) :
    ((limbEntry (localQM31Limbs value) limb).val : ExactM31) =
      exactQM31Limb (qm31ToExact value) limb := by
  fin_cases limb <;>
    rfl

def pTerminalValue (expected : Fin 12 → ExactQM31) (scale : ExactQM31)
    (column : Fin 12) : ExactQM31 :=
  if hcolumn : column.val < 11 then
    scale * (expected ⟨column.val + 1, by omega⟩ - expected 0)
  else 0

def WriteTerminalPrefix (before current : LocalAMatrix)
    (terminal count : Nat) (target : Fin 12 → ExactQM31) : Prop :=
  ∀ row column : Fin 12,
    if 4 * terminal ≤ row.val ∧ row.val < 4 * terminal + 4 ∧
        column.val < count then
      ((matrixEntry current row column).val : ExactM31) =
        exactQM31Limb (target column)
          ⟨(row.val - 4 * terminal) % 4, Nat.mod_lt _ (by omega)⟩
    else
      matrixEntry current row column = matrixEntry before row column

theorem writeTerminalPrefix_zero (matrix : LocalAMatrix)
    (terminal : Nat) (target : Fin 12 → ExactQM31) :
    WriteTerminalPrefix matrix matrix terminal 0 target := by
  intro row column
  rw [if_neg (by omega)]

theorem writeTerminalPrefix_extend (before current next : LocalAMatrix)
    (terminal direction : Nat) (hdirection : direction < 12)
    (limbs : LocalLimbs) (target : Fin 12 → ExactQM31)
    (hprefix : WriteTerminalPrefix before current terminal direction target)
    (hcolumn : WriteLimbPrefix current next terminal direction 4 limbs)
    (hlimbs : ∀ limb : Fin 4,
      ((limbEntry limbs limb).val : ExactM31) =
        exactQM31Limb (target ⟨direction, by omega⟩) limb) :
    WriteTerminalPrefix before next terminal (direction + 1) target := by
  intro row column
  rw [hcolumn row column]
  by_cases hnewCell : column.val = direction ∧
      4 * terminal ≤ row.val ∧ row.val < 4 * terminal + 4
  · rw [if_pos hnewCell]
    rw [if_pos (by
      exact ⟨hnewCell.2.1, hnewCell.2.2, by omega⟩)]
    have hcolumnFin : column = ⟨direction, by omega⟩ :=
      Fin.ext hnewCell.1
    rw [hcolumnFin]
    exact hlimbs _
  · rw [if_neg hnewCell]
    unfold WriteTerminalPrefix at hprefix
    specialize hprefix row column
    by_cases hold : 4 * terminal ≤ row.val ∧
        row.val < 4 * terminal + 4 ∧ column.val < direction
    · rw [if_pos hold] at hprefix
      rw [if_pos (by exact ⟨hold.1, hold.2.1, by omega⟩)]
      exact hprefix
    · rw [if_neg hold] at hprefix
      rw [if_neg]
      · exact hprefix
      · intro hactive
        apply hnewCell
        have hcolumnEq : column.val = direction := by omega
        exact ⟨hcolumnEq, hactive.1, hactive.2.1⟩

def DirectionLoopInvariant (before current : LocalAMatrix)
    (terminal : Fin 3) (runtimeDirection : Std.Usize)
    (expected : Fin 12 → ExactQM31) (scaleExact : ExactQM31) : Prop :=
  runtimeDirection.val ≤ 11 ∧
  WriteTerminalPrefix before current terminal.val runtimeDirection.val
    (pTerminalValue expected scaleExact)

abbrev directionBody :=
  v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0.body

abbrev directionLoop :=
  v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0

theorem directionBody_step (before current : LocalAMatrix)
    (dots : LocalDots) (expected : Fin 12 → ExactQM31)
    (hdots : DotsPrefixExact dots expected 12)
    (scales : v5_cu_probe.good_gate_probe.PreparedTerminalScales)
    (localScale : LocalQM31) (scaleExact : ExactQM31)
    (hscaleCanonical : CanonicalLocalQM31 localScale)
    (hscaleExact : qm31ToExact localScale = scaleExact)
    (hprepared : PreparedFor scales.a_p localScale)
    (runtimeTerminal runtimeDirection : Std.Usize) (terminal : Fin 3)
    (hruntimeTerminal : runtimeTerminal.val = terminal.val)
    (hinvariant : DirectionLoopInvariant before current terminal
      runtimeDirection expected scaleExact)
    (hcontinue : runtimeDirection.val < 11) :
    ∃ nextMatrix : LocalAMatrix, ∃ nextDirection : Std.Usize,
      directionBody dots scales runtimeTerminal current runtimeDirection =
        .ok (.cont (nextMatrix, nextDirection)) ∧
      nextDirection.val = runtimeDirection.val + 1 ∧
      DirectionLoopInvariant before nextMatrix terminal nextDirection expected
        scaleExact := by
  let direction : Fin 12 := ⟨runtimeDirection.val, by omega⟩
  let nextDot : Fin 12 := ⟨runtimeDirection.val + 1, by omega⟩
  have hdirectionCall : Array.index_usize dots runtimeDirection =
      .ok (dotEntry dots direction) := by
    simpa [direction] using
      dots_index_call dots runtimeDirection (by omega)
  let runtimeNextDot := Std.Usize.wrapping_add runtimeDirection 1#usize
  have hnextDot : runtimeNextDot.val = nextDot.val := by
    unfold runtimeNextDot nextDot
    rw [Std.Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits, hp] <;>
      omega
  have hnextDotCall : Array.index_usize dots runtimeNextDot =
      .ok (dotEntry dots nextDot) := by
    simpa [hnextDot] using
      dots_index_call dots runtimeNextDot (by rw [hnextDot]; exact nextDot.isLt)
  have hzeroCall : Array.index_usize dots 0#usize =
      .ok (dotEntry dots 0) := by
    simpa using dots_index_call dots 0#usize (by norm_num)
  have hnextDotInfo := hdots nextDot nextDot.isLt
  have hzeroInfo := hdots 0 (by norm_num)
  obtain ⟨difference, hdifferenceCall, hdifferenceCanonical,
      hdifferenceExact⟩ :=
    local_qm31_sub_corresponds (dotEntry dots nextDot) (dotEntry dots 0)
      hnextDotInfo.1 hzeroInfo.1
  obtain ⟨value, hvalueCall, hvalueCanonical, hvalueExact⟩ :=
    local_prepared_mul_corresponds scales.a_p localScale difference hprepared
      hscaleCanonical hdifferenceCanonical
  let limbs := localQM31Limbs value
  have hlimbsCall :
      v5_cu_probe.good_gate_probe.m31_coordinates value = .ok limbs := by
    simpa [limbs] using m31_coordinates_call value
  have hvalueTarget : qm31ToExact value =
      pTerminalValue expected scaleExact direction := by
    rw [hvalueExact, hscaleExact, hdifferenceExact,
      hnextDotInfo.2, hzeroInfo.2]
    unfold pTerminalValue
    rw [dif_pos hcontinue]
  have hlimbsExact : ∀ limb : Fin 4,
      ((limbEntry limbs limb).val : ExactM31) =
        exactQM31Limb (pTerminalValue expected scaleExact direction) limb := by
    intro limb
    rw [localQM31Limbs_exact, hvalueTarget]
  have hinitialWrite : WriteLimbPrefix current current terminal.val
      direction.val 0 limbs := by
    intro row column
    rw [if_neg (by omega)]
  obtain ⟨nextMatrix, hwriteCall, hwrite⟩ :=
    writeLimbLoop_spec current current runtimeTerminal runtimeDirection
      terminal direction hruntimeTerminal rfl limbs 0#usize (by norm_num)
      hinitialWrite
  let nextDirection := Std.Usize.wrapping_add runtimeDirection 1#usize
  have hnextDirection : nextDirection.val = runtimeDirection.val + 1 := by
    unfold nextDirection
    rw [Std.Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits, hp] <;>
      omega
  have hnextPrefix : WriteTerminalPrefix before nextMatrix terminal.val
      (direction.val + 1) (pTerminalValue expected scaleExact) :=
    writeTerminalPrefix_extend before current nextMatrix terminal.val
      direction.val (by dsimp [direction]; omega) limbs _ hinvariant.2 hwrite
      hlimbsExact
  refine ⟨nextMatrix, nextDirection, ?_, hnextDirection, ?_⟩
  · unfold directionBody
    unfold v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0.body
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
    have hcondition : runtimeDirection <
        Std.Usize.wrapping_sub
          v5_cu_probe.good_gate_probe.GOOD_A_SIZE 1#usize := by
      have hlimit : (Std.Usize.wrapping_sub
          v5_cu_probe.good_gate_probe.GOOD_A_SIZE 1#usize).val = 11 := by
        rw [Std.Usize.wrapping_sub_val_eq]
        rcases System.Platform.numBits_eq with hp | hp <;>
          norm_num [v5_cu_probe.good_gate_probe.GOOD_A_SIZE,
            UScalar.size, Std.Usize.size, Std.Usize.numBits, hp]
      apply (UScalar.lt_equiv _ _).2
      rw [hlimit]
      exact hcontinue
    rw [if_pos hcondition]
    change (do
      let q ← Array.index_usize dots runtimeNextDot
      let q1 ← Array.index_usize dots 0#usize
      let q2 ← aspis_verifier.aspis_core.field.QM31.sub q q1
      let value ←
        aspis_verifier.aspis_core.field.PreparedQm31Multiplier.mul scales.a_p q2
      let limbs ← v5_cu_probe.good_gate_probe.m31_coordinates value
      let a_matrix1 ← writeLimbLoop current runtimeTerminal runtimeDirection
        limbs 0#usize
      let direction1 ← lift
        (Std.Usize.wrapping_add runtimeDirection 1#usize)
      ok (cont (a_matrix1, direction1))) = _
    rw [hnextDotCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hzeroCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hdifferenceCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hvalueCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hlimbsCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hwriteCall]
    rfl
  · constructor
    · rw [hnextDirection]
      omega
    · simpa [hnextDirection] using hnextPrefix

theorem directionLoop_spec (before current : LocalAMatrix)
    (dots : LocalDots) (expected : Fin 12 → ExactQM31)
    (hdots : DotsPrefixExact dots expected 12)
    (scales : v5_cu_probe.good_gate_probe.PreparedTerminalScales)
    (localScale : LocalQM31) (scaleExact : ExactQM31)
    (hscaleCanonical : CanonicalLocalQM31 localScale)
    (hscaleExact : qm31ToExact localScale = scaleExact)
    (hprepared : PreparedFor scales.a_p localScale)
    (runtimeTerminal runtimeDirection : Std.Usize) (terminal : Fin 3)
    (hruntimeTerminal : runtimeTerminal.val = terminal.val)
    (hinvariant : DirectionLoopInvariant before current terminal
      runtimeDirection expected scaleExact) :
    ∃ finalMatrix : LocalAMatrix,
      directionLoop current dots scales runtimeTerminal runtimeDirection =
        .ok (finalMatrix, scales) ∧
      WriteTerminalPrefix before finalMatrix terminal.val 11
        (pTerminalValue expected scaleExact) := by
  by_cases hcontinue : runtimeDirection.val < 11
  · obtain ⟨nextMatrix, nextDirection, hbody, hnextDirection,
      hnextInvariant⟩ :=
      directionBody_step before current dots expected hdots scales localScale
        scaleExact hscaleCanonical hscaleExact hprepared runtimeTerminal
        runtimeDirection terminal hruntimeTerminal hinvariant hcontinue
    obtain ⟨finalMatrix, hloop, hfinal⟩ :=
      directionLoop_spec before nextMatrix dots expected hdots scales localScale
        scaleExact hscaleCanonical hscaleExact hprepared runtimeTerminal
        nextDirection terminal hruntimeTerminal hnextInvariant
    refine ⟨finalMatrix, ?_, hfinal⟩
    change
      v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0.body dots
          scales runtimeTerminal current runtimeDirection =
        .ok (.cont (nextMatrix, nextDirection)) at hbody
    unfold directionLoop
    unfold v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0
    rw [loop.eq_def]
    simp only
    rw [hbody]
    exact hloop
  · have hfinalDirection : runtimeDirection.val = 11 := by
      have hupper := hinvariant.1
      omega
    have hcondition : ¬runtimeDirection <
        Std.Usize.wrapping_sub
          v5_cu_probe.good_gate_probe.GOOD_A_SIZE 1#usize := by
      have hlimit : (Std.Usize.wrapping_sub
          v5_cu_probe.good_gate_probe.GOOD_A_SIZE 1#usize).val = 11 := by
        rw [Std.Usize.wrapping_sub_val_eq]
        rcases System.Platform.numBits_eq with hp | hp <;>
          norm_num [v5_cu_probe.good_gate_probe.GOOD_A_SIZE,
            UScalar.size, Std.Usize.size, Std.Usize.numBits, hp]
      intro hlt
      apply hcontinue
      have := (UScalar.lt_equiv _ _).1 hlt
      rw [hlimit] at this
      exact this
    have hbody : directionBody dots scales runtimeTerminal current
        runtimeDirection = .ok (.done (current, scales)) := by
      unfold directionBody
      unfold v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0.body
      simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
      rw [if_neg hcondition]
    refine ⟨current, ?_, ?_⟩
    · change
        v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0.body dots
            scales runtimeTerminal current runtimeDirection =
          .ok (.done (current, scales)) at hbody
      unfold directionLoop
      unfold v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0
      rw [loop.eq_def]
      simp only
      rw [hbody]
    · simpa [hfinalDirection] using hinvariant.2
termination_by 11 - runtimeDirection.val
decreasing_by
  rw [hnextDirection]
  omega

def terminalValue (expected : Fin 12 → ExactQM31)
    (pScale qScale : ExactQM31) (column : Fin 12) : ExactQM31 :=
  if hcolumn : column.val < 11 then
    pScale * (expected ⟨column.val + 1, by omega⟩ - expected 0)
  else
    qScale * (expected 1 - expected 0)

theorem pTerminalValue_eq_terminalValue (expected : Fin 12 → ExactQM31)
    (pScale qScale : ExactQM31) (column : Fin 12)
    (hcolumn : column.val < 11) :
    pTerminalValue expected pScale column =
      terminalValue expected pScale qScale column := by
  unfold pTerminalValue terminalValue
  rw [dif_pos hcolumn, dif_pos hcolumn]

theorem writeTerminalPrefix_change_target (before current : LocalAMatrix)
    (terminal count : Nat) (first second : Fin 12 → ExactQM31)
    (hcount : count ≤ 12)
    (hprefix : WriteTerminalPrefix before current terminal count first)
    (htarget : ∀ column : Fin 12, column.val < count →
      first column = second column) :
    WriteTerminalPrefix before current terminal count second := by
  unfold WriteTerminalPrefix at hprefix ⊢
  intro row column
  specialize hprefix row column
  by_cases hactive : 4 * terminal ≤ row.val ∧
      row.val < 4 * terminal + 4 ∧ column.val < count
  · rw [if_pos hactive] at hprefix ⊢
    rw [← htarget column hactive.2.2]
    exact hprefix
  · rw [if_neg hactive] at hprefix ⊢
    exact hprefix

abbrev LocalBRow := Array LocalQM31 4#usize
abbrev LocalBMatrix := Array LocalBRow 4#usize

def bMatrixRowEntry (matrix : LocalBMatrix) (row : Fin 4) : LocalBRow :=
  matrix.val[row.val]'(by rw [matrix.property]; exact row.isLt)

theorem bMatrix_index_mut_call (matrix : LocalBMatrix)
    (runtimeRow : Std.Usize) (hrow : runtimeRow.val < 4) :
    Array.index_mut_usize matrix runtimeRow =
      .ok (bMatrixRowEntry matrix ⟨runtimeRow.val, hrow⟩,
        matrix.set runtimeRow) := by
  unfold Array.index_mut_usize
  have hcall := Array.index_usize_eq_ok_of_getElem_eq matrix runtimeRow
    (by rw [matrix.property]; exact hrow)
    (bMatrixRowEntry matrix ⟨runtimeRow.val, hrow⟩)
    (by rfl)
  rw [hcall]
  simp only [Aeneas.Std.bind_tc_ok]

theorem bRow_update_call (rowValues : LocalBRow)
    (runtimeColumn : Std.Usize) (hcolumn : runtimeColumn.val < 4)
    (value : LocalQM31) :
    Array.update rowValues runtimeColumn value =
      .ok (rowValues.set runtimeColumn value) := by
  exact Array.update_eq_ok rowValues runtimeColumn value
    (by rw [rowValues.property]; exact hcolumn)

abbrev bTerminalBody :=
  v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop2.body

abbrev bTerminalLoop :=
  v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop2

theorem bTerminalBody_step (current : LocalBMatrix) (dots : LocalDots)
    (expected : Fin 12 → ExactQM31)
    (hdots : DotsPrefixExact dots expected 12)
    (prepared : _root_.aspis_core.field.PreparedQm31Multiplier)
    (left : LocalQM31) (hleftCanonical : CanonicalLocalQM31 left)
    (hprepared : PreparedFor prepared left)
    (runtimeTerminal runtimeDirection : Std.Usize) (terminal : Fin 3)
    (hruntimeTerminal : runtimeTerminal.val = terminal.val)
    (hcontinue : runtimeDirection.val < 4) :
    ∃ nextMatrix : LocalBMatrix, ∃ nextDirection : Std.Usize,
      bTerminalBody dots prepared runtimeTerminal current runtimeDirection =
        .ok (.cont (nextMatrix, nextDirection)) ∧
      nextDirection.val = runtimeDirection.val + 1 := by
  let direction : Fin 12 := ⟨runtimeDirection.val, by omega⟩
  obtain ⟨hdotCanonical, _⟩ := hdots direction (by omega)
  obtain ⟨value, hvalueCall, _, _⟩ :=
    local_prepared_mul_corresponds prepared left (dotEntry dots direction)
      hprepared hleftCanonical hdotCanonical
  let runtimeRow := Std.Usize.wrapping_add runtimeTerminal 1#usize
  have hrow : runtimeRow.val = terminal.val + 1 := by
    unfold runtimeRow
    rw [Std.Usize.wrapping_add_val_eq, hruntimeTerminal]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits, hp] <;>
      omega
  have hrowBound : runtimeRow.val < 4 := by
    rw [hrow]
    have := terminal.isLt
    omega
  let nextRow :=
    (bMatrixRowEntry current ⟨runtimeRow.val, hrowBound⟩).set
      runtimeDirection value
  let nextMatrix := current.set runtimeRow nextRow
  let nextDirection := Std.Usize.wrapping_add runtimeDirection 1#usize
  have hnextDirection : nextDirection.val = runtimeDirection.val + 1 := by
    unfold nextDirection
    rw [Std.Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits, hp] <;>
      omega
  have hdotCall : Array.index_usize dots runtimeDirection =
      .ok (dotEntry dots direction) := by
    simpa [direction] using dots_index_call dots runtimeDirection (by omega)
  have hmatrixCall : Array.index_mut_usize current runtimeRow =
      .ok (bMatrixRowEntry current ⟨runtimeRow.val, hrowBound⟩,
        current.set runtimeRow) :=
    bMatrix_index_mut_call current runtimeRow hrowBound
  have hrowUpdate : Array.update
      (bMatrixRowEntry current ⟨runtimeRow.val, hrowBound⟩)
      runtimeDirection value = .ok nextRow := by
    simpa [nextRow] using bRow_update_call
      (bMatrixRowEntry current ⟨runtimeRow.val, hrowBound⟩)
      runtimeDirection hcontinue value
  refine ⟨nextMatrix, nextDirection, ?_, hnextDirection⟩
  unfold bTerminalBody
  unfold
    v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop2.body
  have hcondition : runtimeDirection <
      v5_cu_probe.good_gate_probe.GOOD_B_SIZE := by
    apply (UScalar.lt_equiv _ _).2
    simpa [v5_cu_probe.good_gate_probe.GOOD_B_SIZE] using hcontinue
  rw [if_pos hcondition, hdotCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hvalueCall]
  simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.lift]
  change (do
    let (row, back) ← Array.index_mut_usize current runtimeRow
    let row' ← Array.update row runtimeDirection value
    let direction' ← lift nextDirection
    ok (cont (back row', direction'))) = _
  rw [hmatrixCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hrowUpdate]
  rfl

theorem bTerminalLoop_total (current : LocalBMatrix) (dots : LocalDots)
    (expected : Fin 12 → ExactQM31)
    (hdots : DotsPrefixExact dots expected 12)
    (prepared : _root_.aspis_core.field.PreparedQm31Multiplier)
    (left : LocalQM31) (hleftCanonical : CanonicalLocalQM31 left)
    (hprepared : PreparedFor prepared left)
    (runtimeTerminal runtimeDirection : Std.Usize) (terminal : Fin 3)
    (hruntimeTerminal : runtimeTerminal.val = terminal.val)
    (hdirectionBound : runtimeDirection.val ≤ 4) :
    ∃ finalMatrix : LocalBMatrix,
      bTerminalLoop current dots prepared runtimeTerminal runtimeDirection =
        .ok finalMatrix := by
  by_cases hcontinue : runtimeDirection.val < 4
  · obtain ⟨nextMatrix, nextDirection, hbody, hnextDirection⟩ :=
      bTerminalBody_step current dots expected hdots prepared left
        hleftCanonical hprepared runtimeTerminal runtimeDirection terminal
        hruntimeTerminal hcontinue
    obtain ⟨finalMatrix, hloop⟩ :=
      bTerminalLoop_total nextMatrix dots expected hdots prepared left
        hleftCanonical hprepared runtimeTerminal nextDirection terminal
        hruntimeTerminal (by rw [hnextDirection]; omega)
    refine ⟨finalMatrix, ?_⟩
    change
      v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop2.body
          dots prepared runtimeTerminal current runtimeDirection =
        .ok (.cont (nextMatrix, nextDirection)) at hbody
    unfold bTerminalLoop
    unfold v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop2
    rw [loop.eq_def]
    simp only
    rw [hbody]
    exact hloop
  · have hfinalDirection : runtimeDirection.val = 4 := by omega
    have hcondition : ¬runtimeDirection <
        v5_cu_probe.good_gate_probe.GOOD_B_SIZE := by
      intro hlt
      apply hcontinue
      have := (UScalar.lt_equiv _ _).1 hlt
      simpa [v5_cu_probe.good_gate_probe.GOOD_B_SIZE] using this
    have hbody : bTerminalBody dots prepared runtimeTerminal current
        runtimeDirection = .ok (.done current) := by
      unfold bTerminalBody
      unfold
        v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop2.body
      rw [if_neg hcondition]
    refine ⟨current, ?_⟩
    change
      v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop2.body
          dots prepared runtimeTerminal current runtimeDirection =
        .ok (.done current) at hbody
    unfold bTerminalLoop
    unfold v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop2
    rw [loop.eq_def]
    simp only
    rw [hbody]
termination_by 4 - runtimeDirection.val
decreasing_by
  rw [hnextDirection]
  omega

theorem qWriteBody_eq_writeLimbBody
    (matrix : LocalAMatrix) (terminal limb : Std.Usize)
    (limbs : LocalLimbs) :
    v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop1.body
        terminal limbs matrix limb =
      v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0_loop0.body
        terminal 11#usize limbs matrix limb := by
  unfold v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop1.body
  unfold
    v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0_loop0.body
  have hcolumn : Std.Usize.wrapping_sub
      v5_cu_probe.good_gate_probe.GOOD_A_SIZE 1#usize = 11#usize := by
    unfold v5_cu_probe.good_gate_probe.GOOD_A_SIZE Std.Usize.wrapping_sub
      UScalar.wrapping_sub
    congr 1
    apply BitVec.eq_of_toNat_eq
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [UScalar.wrapping_sub, UScalarTy.numBits, hp,
        BitVec.toNat_sub]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  rw [hcolumn]

theorem qWriteLoop_eq_writeLimbLoop
    (matrix : LocalAMatrix) (terminal limb : Std.Usize)
    (limbs : LocalLimbs) :
    v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop1
        matrix terminal limbs limb =
      writeLimbLoop matrix terminal 11#usize limbs limb := by
  have hbody :
      (fun (state : LocalAMatrix × Std.Usize) =>
        v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop1.body
          terminal limbs state.1 state.2) =
      (fun (state : LocalAMatrix × Std.Usize) =>
        v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0_loop0.body
          terminal 11#usize limbs state.1 state.2) := by
    funext state
    exact qWriteBody_eq_writeLimbBody state.1 terminal state.2 limbs
  unfold v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop1
  unfold writeLimbLoop
  unfold
    v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0_loop0
  rw [hbody]

theorem fill_good_terminal_from_dots_a_spec
    (before : LocalAMatrix) (bMatrix : LocalBMatrix) (dots : LocalDots)
    (expected : Fin 12 → ExactQM31)
    (hdots : DotsPrefixExact dots expected 12)
    (scales : v5_cu_probe.good_gate_probe.PreparedTerminalScales)
    (aP aQ bP : LocalQM31) (pScale qScale : ExactQM31)
    (haPCanonical : CanonicalLocalQM31 aP)
    (haQCanonical : CanonicalLocalQM31 aQ)
    (hbPCanonical : CanonicalLocalQM31 bP)
    (haPExact : qm31ToExact aP = pScale)
    (haQExact : qm31ToExact aQ = qScale)
    (haPPrepared : PreparedFor scales.a_p aP)
    (haQPrepared : PreparedFor scales.a_q aQ)
    (hbPPrepared : PreparedFor scales.b_p bP)
    (runtimeTerminal : Std.Usize) (terminal : Fin 3)
    (hruntimeTerminal : runtimeTerminal.val = terminal.val) :
    ∃ finalA : LocalAMatrix, ∃ finalB : LocalBMatrix,
      v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots
          before bMatrix dots scales runtimeTerminal = .ok (finalA, finalB) ∧
      WriteTerminalPrefix before finalA terminal.val 12
        (terminalValue expected pScale qScale) := by
  have hinitial : DirectionLoopInvariant before before terminal 0#usize
      expected pScale := by
    exact ⟨by norm_num, writeTerminalPrefix_zero before terminal.val _⟩
  obtain ⟨pMatrix, hpCall, hpPrefix⟩ :=
    directionLoop_spec before before dots expected hdots scales aP pScale
      haPCanonical haPExact haPPrepared runtimeTerminal 0#usize terminal
      hruntimeTerminal hinitial
  have hpTarget : WriteTerminalPrefix before pMatrix terminal.val 11
      (terminalValue expected pScale qScale) :=
    writeTerminalPrefix_change_target before pMatrix terminal.val 11
      (pTerminalValue expected pScale)
      (terminalValue expected pScale qScale) (by norm_num) hpPrefix
      (fun column hcolumn =>
        pTerminalValue_eq_terminalValue expected pScale qScale column hcolumn)
  have hdotOne := hdots (1 : Fin 12) (by norm_num)
  have hdotZero := hdots (0 : Fin 12) (by norm_num)
  have hdotOneCall : Array.index_usize dots 1#usize =
      .ok (dotEntry dots 1) := by
    simpa using dots_index_call dots 1#usize (by norm_num)
  have hdotZeroCall : Array.index_usize dots 0#usize =
      .ok (dotEntry dots 0) := by
    simpa using dots_index_call dots 0#usize (by norm_num)
  obtain ⟨difference, hdifferenceCall, hdifferenceCanonical,
      hdifferenceExact⟩ :=
    local_qm31_sub_corresponds (dotEntry dots 1) (dotEntry dots 0)
      hdotOne.1 hdotZero.1
  obtain ⟨qValue, hqValueCall, hqValueCanonical, hqValueExact⟩ :=
    local_prepared_mul_corresponds scales.a_q aQ difference
      haQPrepared haQCanonical hdifferenceCanonical
  let qLimbs := localQM31Limbs qValue
  have hqLimbsCall :
      v5_cu_probe.good_gate_probe.m31_coordinates qValue = .ok qLimbs := by
    simpa [qLimbs] using m31_coordinates_call qValue
  have hqInitialWrite : WriteLimbPrefix pMatrix pMatrix terminal.val 11
      0 qLimbs := by
    intro row column
    rw [if_neg (by omega)]
  obtain ⟨qMatrix, hqWriteCall, hqWrite⟩ :=
    writeLimbLoop_spec pMatrix pMatrix runtimeTerminal 11#usize terminal
      (11 : Fin 12) hruntimeTerminal rfl qLimbs 0#usize (by norm_num)
      hqInitialWrite
  have hqWriteGenerated :
      v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop1
          pMatrix runtimeTerminal qLimbs 0#usize = .ok qMatrix := by
    rw [qWriteLoop_eq_writeLimbLoop]
    exact hqWriteCall
  have hqLimbsExact : ∀ limb : Fin 4,
      ((limbEntry qLimbs limb).val : ExactM31) =
        exactQM31Limb (terminalValue expected pScale qScale 11) limb := by
    intro limb
    rw [show ((limbEntry qLimbs limb).val : ExactM31) =
        exactQM31Limb (qm31ToExact qValue) limb by
      simpa [qLimbs] using localQM31Limbs_exact qValue limb]
    rw [hqValueExact, haQExact, hdifferenceExact, hdotOne.2, hdotZero.2]
    unfold terminalValue
    rw [dif_neg (by norm_num : ¬(11 : Fin 12).val < 11)]
  have hfullPrefix : WriteTerminalPrefix before qMatrix terminal.val 12
      (terminalValue expected pScale qScale) :=
    writeTerminalPrefix_extend before pMatrix qMatrix terminal.val 11
      (by norm_num) qLimbs (terminalValue expected pScale qScale)
      hpTarget hqWrite hqLimbsExact
  obtain ⟨finalB, hbCall⟩ :=
    bTerminalLoop_total bMatrix dots expected hdots scales.b_p bP
      hbPCanonical hbPPrepared runtimeTerminal 0#usize terminal
      hruntimeTerminal (by norm_num)
  change
    v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop0
        before dots scales runtimeTerminal 0#usize = .ok (pMatrix, scales)
    at hpCall
  change
    v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots_loop2
        bMatrix dots scales.b_p runtimeTerminal 0#usize = .ok finalB
    at hbCall
  refine ⟨qMatrix, finalB, ?_, hfullPrefix⟩
  unfold v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots
  rw [hpCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hdotOneCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hdotZeroCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hdifferenceCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hqValueCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hqLimbsCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hqWriteGenerated]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hbCall]
  simp only [Aeneas.Std.bind_tc_ok]

theorem base_terminalValue_eq_assembled (column : Fin 12) :
    terminalValue (fun shift => exactDotFor weights shift 0)
        (exactAPFor point) (exactAQFor point) column =
      assembledTerminalValue 0 column := by
  rw [baseDots_exact, point_aP_exact, point_aQ_exact]
  rfl

theorem xor_terminalValue_eq_assembled (column : Fin 12) :
    terminalValue (fun shift => exactDotFor weights shift 6)
        (exactAPFor point) (exactAQFor point) column =
      assembledTerminalValue 2 column := by
  rw [xorDots_exact, point_aP_exact, point_aQ_exact]
  rfl

theorem successor_terminalValue_eq_assembled (column : Fin 12) :
    terminalValue (fun shift => exactDotFor successorWeights shift 0)
        (exactAPFor successor) (exactAQFor successor) column =
      assembledTerminalValue 1 column := by
  rw [successorDots_exact, successor_aP_exact, successor_aQ_exact]
  rfl

theorem fill_good_base_and_xor_terminals_concrete_a_spec
    (before : LocalAMatrix) (bMatrix : LocalBMatrix)
    (directions : Slice LocalNatural)
    (hdirections : ConcreteShiftedSlice directions) :
    ∃ baseMatrix xorMatrix : LocalAMatrix, ∃ finalB : LocalBMatrix,
      v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals
          before bMatrix directions point = .ok (xorMatrix, finalB) ∧
      WriteTerminalPrefix before baseMatrix 0 12
        (assembledTerminalValue 0) ∧
      WriteTerminalPrefix baseMatrix xorMatrix 2 12
        (assembledTerminalValue 2) := by
  obtain ⟨aPrefix, bPrefix, hprefixCall, haPrefixCanonical,
      hbPrefixCanonical, haPrefixExact, _⟩ :=
    deployed_three_bit_prefixes_exact_spec point point_canonical
  let last :=
    GoodMatricesCurrent.SourceExtractedTerminalPrefixes.pointEntry point 9
  have hlastCall : Array.index_usize point 9#usize = .ok last := by
    simpa [last] using
      GoodMatricesCurrent.SourceExtractedTerminalPrefixes.point_index_call
        point 9#usize (by norm_num)
  have hlastCanonical : CanonicalLocalQM31 last := by
    simpa [last,
      GoodMatricesCurrent.SourceExtractedTerminalPrefixes.pointEntry,
      GoodMatricesCurrent.SourceExtractedTerminalWeights.pointEntry] using
      point_canonical (9 : Fin 10)
  have hlastExact : qm31ToExact last =
      GoodMatricesCurrent.SourceExtractedTerminalPrefixes.pointToExact point 9 :=
    rfl
  obtain ⟨scales, hscalesCall, hscales⟩ :=
    prepared_terminal_scales_exact_spec aPrefix bPrefix last
      haPrefixCanonical hbPrefixCanonical hlastCanonical
  rcases hscales with ⟨aP, aQ, bP, haPCanonical, haQCanonical,
    hbPCanonical, haPExact, haQExact, _, haPPrepared, haQPrepared,
    hbPPrepared⟩
  have haPExact' : qm31ToExact aP = exactAPFor point := by
    rw [haPExact, haPrefixExact, hlastExact]
    unfold exactAPFor
    rfl
  have haQExact' : qm31ToExact aQ = exactAQFor point := by
    rw [haQExact, haPrefixExact, hlastExact]
    unfold exactAQFor
    rfl
  let zeroQM31 : LocalQM31 :=
    { c0 := { a := 0#u32, b := 0#u32 },
      c1 := { a := 0#u32, b := 0#u32 } }
  have hzeroCall : aspis_verifier.aspis_core.field.QM31.ZERO =
      .ok zeroQM31 := by
    simpa [zeroQM31] using local_zero_call
  let zeroDots : LocalDots := Array.repeat 12#usize zeroQM31
  have hinitial : BaseXorLoopInvariant zeroDots zeroDots 0#usize := by
    refine ⟨by norm_num, ?_, ?_⟩
    · intro index hindex
      norm_num at hindex
    · intro index hindex
      norm_num at hindex
  obtain ⟨baseDots, xorDots, hdotsCall, hbaseDots, hxorDots⟩ :=
    baseXorLoop_spec directions hdirections zeroDots zeroDots 0#usize hinitial
  obtain ⟨baseMatrix, baseB, hbaseCall, hbasePrefix⟩ :=
    fill_good_terminal_from_dots_a_spec before bMatrix baseDots
      (fun shift => exactDotFor weights shift 0) hbaseDots scales
      aP aQ bP (exactAPFor point) (exactAQFor point)
      haPCanonical haQCanonical hbPCanonical haPExact' haQExact'
      haPPrepared haQPrepared hbPPrepared 0#usize 0 rfl
  obtain ⟨xorMatrix, finalB, hxorCall, hxorPrefix⟩ :=
    fill_good_terminal_from_dots_a_spec baseMatrix baseB xorDots
      (fun shift => exactDotFor weights shift 6) hxorDots scales
      aP aQ bP (exactAPFor point) (exactAQFor point)
      haPCanonical haQCanonical hbPCanonical haPExact' haQExact'
      haPPrepared haQPrepared hbPPrepared 2#usize 2 rfl
  have hbaseAssembled : WriteTerminalPrefix before baseMatrix 0 12
      (assembledTerminalValue 0) :=
    writeTerminalPrefix_change_target before baseMatrix 0 12
      (terminalValue (fun shift => exactDotFor weights shift 0)
        (exactAPFor point) (exactAQFor point))
      (assembledTerminalValue 0) (by norm_num) hbasePrefix
      (fun column _ => base_terminalValue_eq_assembled column)
  have hxorAssembled : WriteTerminalPrefix baseMatrix xorMatrix 2 12
      (assembledTerminalValue 2) :=
    writeTerminalPrefix_change_target baseMatrix xorMatrix 2 12
      (terminalValue (fun shift => exactDotFor weights shift 6)
        (exactAPFor point) (exactAQFor point))
      (assembledTerminalValue 2) (by norm_num) hxorPrefix
      (fun column _ => xor_terminalValue_eq_assembled column)
  change
    v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals_loop
        directions weights zeroDots zeroDots 0#usize =
      .ok (baseDots, xorDots) at hdotsCall
  refine ⟨baseMatrix, xorMatrix, finalB, ?_, hbaseAssembled,
    hxorAssembled⟩
  unfold v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals
  rw [weights_call]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hprefixCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hlastCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hscalesCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hzeroCall]
  simp only [Aeneas.Std.bind_tc_ok]
  change (do
    let (baseDots', xorDots') ←
      v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals_loop
        directions weights zeroDots zeroDots 0#usize
    let (baseMatrix', baseB') ←
      v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots
        before bMatrix baseDots' scales 0#usize
    v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots
      baseMatrix' baseB' xorDots' scales 2#usize) = _
  rw [hdotsCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hbaseCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hxorCall]

theorem fill_good_successor_terminal_concrete_a_spec
    (before : LocalAMatrix) (bMatrix : LocalBMatrix)
    (directions : Slice LocalNatural)
    (hdirections : ConcreteShiftedSlice directions) :
    ∃ finalA : LocalAMatrix, ∃ finalB : LocalBMatrix,
      v5_cu_probe.good_gate_probe.fill_good_successor_terminal
          before bMatrix directions successor = .ok (finalA, finalB) ∧
      WriteTerminalPrefix before finalA 1 12
        (assembledTerminalValue 1) := by
  have hsuccessorCanonical :
      GoodMatricesCurrent.SourceExtractedTerminalPrefixes.CanonicalLocalPoint
        successor := by
    intro index
    fin_cases index <;>
      norm_num [successor,
        GoodMatricesCurrent.SourceExtractedTerminalPrefixes.pointEntry,
        q, Aeneas.Std.Array.make, CanonicalLocalQM31,
        CanonicalLocalCM31, CanonicalLocalM31,
        AspisV5ComponentCQM31TowerExact.P]
  obtain ⟨aPrefix, bPrefix, hprefixCall, haPrefixCanonical,
      hbPrefixCanonical, haPrefixExact, _⟩ :=
    deployed_three_bit_prefixes_exact_spec successor hsuccessorCanonical
  let last :=
    GoodMatricesCurrent.SourceExtractedTerminalPrefixes.pointEntry successor 9
  have hlastCall : Array.index_usize successor 9#usize = .ok last := by
    simpa [last] using
      GoodMatricesCurrent.SourceExtractedTerminalPrefixes.point_index_call
        successor 9#usize (by norm_num)
  have hlastCanonical : CanonicalLocalQM31 last := hsuccessorCanonical 9
  have hlastExact : qm31ToExact last =
      GoodMatricesCurrent.SourceExtractedTerminalPrefixes.pointToExact
        successor 9 := rfl
  obtain ⟨scales, hscalesCall, hscales⟩ :=
    prepared_terminal_scales_exact_spec aPrefix bPrefix last
      haPrefixCanonical hbPrefixCanonical hlastCanonical
  rcases hscales with ⟨aP, aQ, bP, haPCanonical, haQCanonical,
    hbPCanonical, haPExact, haQExact, _, haPPrepared, haQPrepared,
    hbPPrepared⟩
  have haPExact' : qm31ToExact aP = exactAPFor successor := by
    rw [haPExact, haPrefixExact, hlastExact]
    unfold exactAPFor
    rfl
  have haQExact' : qm31ToExact aQ = exactAQFor successor := by
    rw [haQExact, haPrefixExact, hlastExact]
    unfold exactAQFor
    rfl
  let zeroQM31 : LocalQM31 :=
    { c0 := { a := 0#u32, b := 0#u32 },
      c1 := { a := 0#u32, b := 0#u32 } }
  have hzeroCall : aspis_verifier.aspis_core.field.QM31.ZERO =
      .ok zeroQM31 := by
    simpa [zeroQM31] using local_zero_call
  let zeroDots : LocalDots := Array.repeat 12#usize zeroQM31
  have hinitial : SuccessorLoopInvariant zeroDots 0#usize := by
    refine ⟨by norm_num, ?_⟩
    intro index hindex
    norm_num at hindex
  obtain ⟨dots, hdotsCall, hdots⟩ :=
    successorLoop_spec directions hdirections zeroDots 0#usize hinitial
  obtain ⟨finalA, finalB, hfillCall, hprefix⟩ :=
    fill_good_terminal_from_dots_a_spec before bMatrix dots
      (fun shift => exactDotFor successorWeights shift 0) hdots scales
      aP aQ bP (exactAPFor successor) (exactAQFor successor)
      haPCanonical haQCanonical hbPCanonical haPExact' haQExact'
      haPPrepared haQPrepared hbPPrepared 1#usize 1 rfl
  have hassembled : WriteTerminalPrefix before finalA 1 12
      (assembledTerminalValue 1) :=
    writeTerminalPrefix_change_target before finalA 1 12
      (terminalValue (fun shift => exactDotFor successorWeights shift 0)
        (exactAPFor successor) (exactAQFor successor))
      (assembledTerminalValue 1) (by norm_num) hprefix
      (fun column _ => successor_terminalValue_eq_assembled column)
  change
    v5_cu_probe.good_gate_probe.fill_good_successor_terminal_loop
        directions successorWeights zeroDots 0#usize = .ok dots at hdotsCall
  refine ⟨finalA, finalB, ?_, hassembled⟩
  unfold v5_cu_probe.good_gate_probe.fill_good_successor_terminal
  rw [successorWeights_call]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hzeroCall]
  simp only [Aeneas.Std.bind_tc_ok]
  change (do
    let dots' ←
      v5_cu_probe.good_gate_probe.fill_good_successor_terminal_loop
        directions successorWeights zeroDots 0#usize
    let (aPrefix', bPrefix') ←
      v5_cu_probe.good_gate_probe.deployed_three_bit_prefixes successor
    let last' ← Array.index_usize successor 9#usize
    let scales' ←
      v5_cu_probe.good_gate_probe.prepared_terminal_scales
        aPrefix' bPrefix' last'
    v5_cu_probe.good_gate_probe.fill_good_terminal_from_dots
      before bMatrix dots' scales' 1#usize) = _
  rw [hdotsCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hprefixCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hlastCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hscalesCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hfillCall]

def aMatrixToExact (matrix : LocalAMatrix) :
    Matrix (Fin 12) (Fin 12) ExactM31 :=
  fun row column => (matrixEntry matrix row column).val

theorem three_terminal_prefixes_eq_assembled
    (initial baseMatrix xorMatrix finalMatrix : LocalAMatrix)
    (hbase : WriteTerminalPrefix initial baseMatrix 0 12
      (assembledTerminalValue 0))
    (hxor : WriteTerminalPrefix baseMatrix xorMatrix 2 12
      (assembledTerminalValue 2))
    (hsuccessor : WriteTerminalPrefix xorMatrix finalMatrix 1 12
      (assembledTerminalValue 1)) :
    aMatrixToExact finalMatrix = assembledTerminalMatrixFin := by
  funext row column
  unfold aMatrixToExact assembledTerminalMatrixFin
  unfold WriteTerminalPrefix at hbase hxor hsuccessor
  have hcolumn : column.val < 12 := column.isLt
  by_cases hrow0 : row.val < 4
  · have hs := hsuccessor row column
    have hx := hxor row column
    have hb := hbase row column
    rw [if_neg (by omega)] at hs
    rw [if_neg (by omega)] at hx
    rw [if_pos (by omega)] at hb
    rw [hs, hx]
    have hquotient : row.val / 4 = 0 := by omega
    simpa [hquotient] using hb
  · by_cases hrow1 : row.val < 8
    · have hs := hsuccessor row column
      rw [if_pos (by omega)] at hs
      have hquotient : row.val / 4 = 1 := by omega
      have hremainder : (row.val - 4) % 4 = row.val % 4 := by omega
      simpa [hquotient, hremainder] using hs
    · have hs := hsuccessor row column
      have hx := hxor row column
      rw [if_neg (by omega)] at hs
      rw [if_pos (by omega)] at hx
      rw [hs]
      have hquotient : row.val / 4 = 2 := by omega
      have hremainder : (row.val - 8) % 4 = row.val % 4 := by omega
      simpa [hquotient, hremainder] using hx

def InactiveIterBound (iter : core.slice.iter.Iter Std.U8) : Prop :=
  iter.i ≤ iter.slice.val.length ∧
  ∀ (index : Nat) (hindex : index < iter.slice.val.length),
    (iter.slice.val[index]'hindex).val < 48

abbrev inactiveBody :=
  v5_cu_probe.good_gate_probe.evaluate_b_inactive_loop.body

abbrev inactiveLoop :=
  v5_cu_probe.good_gate_probe.evaluate_b_inactive_loop

theorem inactiveBody_step (natural : LocalNatural)
    (iter : core.slice.iter.Iter Std.U8) (raw : Std.U64)
    (hinvariant : InactiveIterBound iter)
    (hcontinue : iter.i < iter.slice.val.length) :
    ∃ nextIter : core.slice.iter.Iter Std.U8, ∃ nextRaw : Std.U64,
      inactiveBody natural iter raw = .ok (.cont (nextIter, nextRaw)) ∧
      InactiveIterBound nextIter ∧
      nextIter.slice = iter.slice ∧ nextIter.i = iter.i + 1 := by
  let index : Std.U8 := iter.slice.val[iter.i]'hcontinue
  let nextIter : core.slice.iter.Iter Std.U8 :=
    { slice := iter.slice, i := iter.i + 1 }
  let runtimeIndex := core.convert.num.FromUsizeU8.from index
  have hruntimeIndex : runtimeIndex.val = index.val := by
    exact core.convert.num.FromUsizeU8.from_val_eq index
  have hindexBound : index.val < 48 := by
    exact hinvariant.2 iter.i hcontinue
  have hruntimeIndexBound : runtimeIndex.val < 48 := by
    rw [hruntimeIndex]
    exact hindexBound
  let value := naturalEntry natural ⟨runtimeIndex.val, hruntimeIndexBound⟩
  have hnaturalCall : Array.index_usize natural runtimeIndex = .ok value := by
    simpa [value] using natural_index_call natural runtimeIndex
      hruntimeIndexBound
  let widened := core.convert.num.FromU64U32.from value
  let nextRaw := Std.U64.wrapping_add raw widened
  have hnextCall : core.slice.iter.IteratorSliceIter.next iter =
      .ok (some index, nextIter) := by
    unfold core.slice.iter.IteratorSliceIter.next
    have hcondition : iter.i < iter.slice.len := by
      change iter.i < iter.slice.len.val
      rw [Slice.len_val]
      exact hcontinue
    rw [dif_pos hcondition]
    rfl
  refine ⟨nextIter, nextRaw, ?_, ?_, rfl, rfl⟩
  · unfold inactiveBody
    unfold v5_cu_probe.good_gate_probe.evaluate_b_inactive_loop.body
    rw [hnextCall]
    simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.lift]
    change (do
      let value' ← Array.index_usize natural runtimeIndex
      let widened' ← lift (core.convert.num.FromU64U32.from value')
      let raw' ← lift (Std.U64.wrapping_add raw widened')
      ok (cont (nextIter, raw'))) = _
    rw [hnaturalCall]
    rfl
  · constructor
    · dsimp [nextIter]
      omega
    · intro output houtputUpper
      exact hinvariant.2 output houtputUpper

theorem inactiveLoop_total (natural : LocalNatural)
    (iter : core.slice.iter.Iter Std.U8) (raw : Std.U64)
    (hinvariant : InactiveIterBound iter) :
    ∃ finalRaw : Std.U64,
      inactiveLoop iter natural raw = .ok finalRaw := by
  by_cases hcontinue : iter.i < iter.slice.val.length
  · obtain ⟨nextIter, nextRaw, hbody, hnextInvariant,
      hnextSlice, hnextIndex⟩ :=
      inactiveBody_step natural iter raw hinvariant hcontinue
    obtain ⟨finalRaw, hloop⟩ :=
      inactiveLoop_total natural nextIter nextRaw hnextInvariant
    refine ⟨finalRaw, ?_⟩
    change
      v5_cu_probe.good_gate_probe.evaluate_b_inactive_loop.body
          natural iter raw = .ok (.cont (nextIter, nextRaw)) at hbody
    unfold inactiveLoop
    unfold v5_cu_probe.good_gate_probe.evaluate_b_inactive_loop
    rw [loop.eq_def]
    simp only
    rw [hbody]
    exact hloop
  · have hfinished : iter.i = iter.slice.val.length := by
      have hupper := hinvariant.1
      omega
    have hnextCall : core.slice.iter.IteratorSliceIter.next iter =
        .ok (none, iter) := by
      unfold core.slice.iter.IteratorSliceIter.next
      have hcondition : ¬iter.i < iter.slice.len := by
        change ¬iter.i < iter.slice.len.val
        rw [Slice.len_val]
        exact hcontinue
      rw [dif_neg hcondition]
    have hbody : inactiveBody natural iter raw = .ok (.done raw) := by
      unfold inactiveBody
      unfold v5_cu_probe.good_gate_probe.evaluate_b_inactive_loop.body
      rw [hnextCall]
      simp only [Aeneas.Std.bind_tc_ok]
    refine ⟨raw, ?_⟩
    change
      v5_cu_probe.good_gate_probe.evaluate_b_inactive_loop.body
          natural iter raw = .ok (.done raw) at hbody
    unfold inactiveLoop
    unfold v5_cu_probe.good_gate_probe.evaluate_b_inactive_loop
    rw [loop.eq_def]
    simp only
    rw [hbody]
termination_by iter.slice.val.length - iter.i
decreasing_by
  rw [hnextSlice, hnextIndex]
  omega

theorem local_m31_reduce_u64_total (raw : Std.U64) :
    ∃ value : GoodMatricesCurrent.SourceExtractedTerminalField.LocalM31,
      aspis_verifier.aspis_core.field.M31.reduce_u64 raw = .ok value := by
  unfold aspis_verifier.aspis_core.field.M31.reduce_u64
  unfold AuthenticFieldPow.field.reduce_u64
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem evaluate_b_inactive_total (natural : LocalNatural) :
    ∃ value : LocalQM31,
      v5_cu_probe.good_gate_probe.evaluate_b_inactive natural = .ok value := by
  let initialIter : core.slice.iter.Iter Std.U8 :=
    { slice := Array.to_slice
        v5_cu_probe.good_gate_probe.B_INACTIVE_NATURAL_SUPPORT,
      i := 0 }
  have hinto :
      SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
          v5_cu_probe.good_gate_probe.B_INACTIVE_NATURAL_SUPPORT =
        .ok initialIter := by
    rfl
  have hinitial : InactiveIterBound initialIter := by
    constructor
    · dsimp [initialIter]
      norm_num [v5_cu_probe.good_gate_probe.B_INACTIVE_NATURAL_SUPPORT,
        Aeneas.Std.Array.make]
    · intro index hindexUpper
      have hindexUpper' : index < 30 := by
        simpa [initialIter, Array.to_slice,
          v5_cu_probe.good_gate_probe.B_INACTIVE_NATURAL_SUPPORT,
          Aeneas.Std.Array.make] using hindexUpper
      interval_cases index <;>
        norm_num [initialIter, Array.to_slice,
          v5_cu_probe.good_gate_probe.B_INACTIVE_NATURAL_SUPPORT,
          Aeneas.Std.Array.make]
  obtain ⟨raw, hloop⟩ := inactiveLoop_total natural initialIter 0#u64 hinitial
  obtain ⟨m31, hm31Call⟩ := local_m31_reduce_u64_total raw
  let cm31 : GoodMatricesCurrent.SourceExtractedTerminalField.LocalCM31 :=
    { a := m31, b := 0#u32 }
  let qm31 : LocalQM31 :=
    { c0 := cm31, c1 := { a := 0#u32, b := 0#u32 } }
  have hcm31Call : aspis_verifier.aspis_core.field.CM31.from_m31 m31 =
      .ok cm31 := by
    rfl
  have hqm31Call : aspis_verifier.aspis_core.field.QM31.from_cm31 cm31 =
      .ok qm31 := by
    rfl
  refine ⟨qm31, ?_⟩
  unfold v5_cu_probe.good_gate_probe.evaluate_b_inactive
  rw [hinto]
  simp only [Aeneas.Std.bind_tc_ok]
  change (do
    let raw' ← inactiveLoop initialIter natural 0#u64
    let m31' ← aspis_verifier.aspis_core.field.M31.reduce_u64 raw'
    let cm31' ← aspis_verifier.aspis_core.field.CM31.from_m31 m31'
    aspis_verifier.aspis_core.field.QM31.from_cm31 cm31') = _
  rw [hloop]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hm31Call]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hcm31Call]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hqm31Call]

abbrev initializeBBody :=
  v5_cu_probe.good_gate_probe.good_matrices_loop.body

abbrev initializeBLoop :=
  v5_cu_probe.good_gate_probe.good_matrices_loop

theorem initializeBBody_step
    (directions : alloc.vec.Vec LocalNatural)
    (hdirections : ConcreteShiftedDirections directions)
    (current : LocalBMatrix) (runtimeDirection : Std.Usize)
    (hcontinue : runtimeDirection.val < 4) :
    ∃ nextMatrix : LocalBMatrix, ∃ nextDirection : Std.Usize,
      initializeBBody directions current runtimeDirection =
        .ok (.cont (nextMatrix, nextDirection)) ∧
      nextDirection.val = runtimeDirection.val + 1 := by
  let direction : Fin 12 := ⟨runtimeDirection.val, by omega⟩
  obtain ⟨natural, hlookup, _, _⟩ := hdirections.2 direction
  have hlookupRuntime :
      directions.val[runtimeDirection.val]? = some natural := by
    simpa [direction] using hlookup
  have hnaturalCall : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice LocalNatural)
      directions runtimeDirection = .ok natural := by
    rw [alloc.vec.Vec.index_slice_index]
    unfold alloc.vec.Vec.index_usize
    rw [alloc.vec.Vec.getElem?_Nat_eq, hlookupRuntime]
  obtain ⟨value, hvalueCall⟩ := evaluate_b_inactive_total natural
  let row := bMatrixRowEntry current 0
  let nextRow := row.set runtimeDirection value
  let nextMatrix := current.set 0#usize nextRow
  let nextDirection := Std.Usize.wrapping_add runtimeDirection 1#usize
  have hnextDirection : nextDirection.val = runtimeDirection.val + 1 := by
    unfold nextDirection
    rw [Std.Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hp | hp <;>
      norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits, hp] <;>
      omega
  have hmatrixCall : Array.index_mut_usize current 0#usize =
      .ok (row, current.set 0#usize) := by
    simpa [row] using bMatrix_index_mut_call current 0#usize (by norm_num)
  have hrowUpdate : Array.update row runtimeDirection value =
      .ok nextRow := by
    simpa [nextRow] using
      bRow_update_call row runtimeDirection hcontinue value
  refine ⟨nextMatrix, nextDirection, ?_, hnextDirection⟩
  unfold initializeBBody
  unfold v5_cu_probe.good_gate_probe.good_matrices_loop.body
  have hcondition : runtimeDirection <
      v5_cu_probe.good_gate_probe.GOOD_B_SIZE := by
    apply (UScalar.lt_equiv _ _).2
    simpa [v5_cu_probe.good_gate_probe.GOOD_B_SIZE] using hcontinue
  rw [if_pos hcondition, hnaturalCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hvalueCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hmatrixCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hrowUpdate]
  rfl

theorem initializeBLoop_total
    (directions : alloc.vec.Vec LocalNatural)
    (hdirections : ConcreteShiftedDirections directions)
    (current : LocalBMatrix) (runtimeDirection : Std.Usize)
    (hdirectionBound : runtimeDirection.val ≤ 4) :
    ∃ finalMatrix : LocalBMatrix,
      initializeBLoop directions current runtimeDirection =
        .ok finalMatrix := by
  by_cases hcontinue : runtimeDirection.val < 4
  · obtain ⟨nextMatrix, nextDirection, hbody, hnextDirection⟩ :=
      initializeBBody_step directions hdirections current runtimeDirection
        hcontinue
    obtain ⟨finalMatrix, hloop⟩ :=
      initializeBLoop_total directions hdirections nextMatrix nextDirection
        (by rw [hnextDirection]; omega)
    refine ⟨finalMatrix, ?_⟩
    change v5_cu_probe.good_gate_probe.good_matrices_loop.body
        directions current runtimeDirection =
      .ok (.cont (nextMatrix, nextDirection)) at hbody
    unfold initializeBLoop
    unfold v5_cu_probe.good_gate_probe.good_matrices_loop
    rw [loop.eq_def]
    simp only
    rw [hbody]
    exact hloop
  · have hcondition : ¬runtimeDirection <
        v5_cu_probe.good_gate_probe.GOOD_B_SIZE := by
      intro hlt
      apply hcontinue
      have := (UScalar.lt_equiv _ _).1 hlt
      simpa [v5_cu_probe.good_gate_probe.GOOD_B_SIZE] using this
    have hbody : initializeBBody directions current runtimeDirection =
        .ok (.done current) := by
      unfold initializeBBody
      unfold v5_cu_probe.good_gate_probe.good_matrices_loop.body
      rw [if_neg hcondition]
    refine ⟨current, ?_⟩
    change v5_cu_probe.good_gate_probe.good_matrices_loop.body
        directions current runtimeDirection = .ok (.done current) at hbody
    unfold initializeBLoop
    unfold v5_cu_probe.good_gate_probe.good_matrices_loop
    rw [loop.eq_def]
    simp only
    rw [hbody]
termination_by 4 - runtimeDirection.val
decreasing_by
  rw [hnextDirection]
  omega

theorem generated_good_matrices_a_projection_eq_printed :
    ∃ finalA : LocalAMatrix, ∃ finalB : LocalBMatrix,
      v5_cu_probe.good_gate_probe.good_matrices kernel point =
        .ok (finalA, finalB) ∧
      aMatrixToExact finalA =
        AspisV5ComponentADeployedTerminalApplicability.ConcreteProbeWitness.printedTerminalMatrixFin := by
  obtain ⟨directions, hdirectionsCall, hdirections⟩ :=
    concrete_good_shifted_directions_spec
  let zeroM31 : GoodMatricesCurrent.SourceExtractedTerminalField.LocalM31 :=
    _root_.aspis_core.field.M31.ZERO
  have hm31ZeroCall : aspis_verifier.aspis_core.field.M31.ZERO =
      .ok zeroM31 := by
    rfl
  let zeroRow : LocalRow := Array.repeat 12#usize zeroM31
  let initialA : LocalAMatrix := Array.repeat 12#usize zeroRow
  let zeroQM31 : LocalQM31 :=
    { c0 := { a := 0#u32, b := 0#u32 },
      c1 := { a := 0#u32, b := 0#u32 } }
  have hqm31ZeroCall : aspis_verifier.aspis_core.field.QM31.ZERO =
      .ok zeroQM31 := by
    simpa [zeroQM31] using local_zero_call
  let zeroBRow : LocalBRow := Array.repeat 4#usize zeroQM31
  let initialB : LocalBMatrix := Array.repeat 4#usize zeroBRow
  obtain ⟨initializedB, hinitializeB⟩ :=
    initializeBLoop_total directions hdirections initialB 0#usize
      (by norm_num)
  let directionSlice := alloc.vec.Vec.deref directions
  have hdirectionSlice : ConcreteShiftedSlice directionSlice :=
    concreteShiftedSlice_deref directions hdirections
  obtain ⟨baseMatrix, xorMatrix, xorB, hbaseXor, hbasePrefix,
      hxorPrefix⟩ :=
    fill_good_base_and_xor_terminals_concrete_a_spec initialA initializedB
      directionSlice hdirectionSlice
  obtain ⟨finalA, finalB, hsuccessorCall, hsuccessorPrefix⟩ :=
    fill_good_successor_terminal_concrete_a_spec xorMatrix xorB
      directionSlice hdirectionSlice
  have hmatrix : aMatrixToExact finalA = assembledTerminalMatrixFin :=
    three_terminal_prefixes_eq_assembled initialA baseMatrix xorMatrix finalA
      hbasePrefix hxorPrefix hsuccessorPrefix
  have hprinted : aMatrixToExact finalA =
      AspisV5ComponentADeployedTerminalApplicability.ConcreteProbeWitness.printedTerminalMatrixFin :=
    hmatrix.trans assembledTerminalMatrixFin_eq_printed
  change v5_cu_probe.good_gate_probe.good_matrices_loop
      directions initialB 0#usize = .ok initializedB at hinitializeB
  refine ⟨finalA, finalB, ?_, hprinted⟩
  unfold v5_cu_probe.good_gate_probe.good_matrices
  rw [hdirectionsCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hm31ZeroCall]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hqm31ZeroCall]
  simp only [Aeneas.Std.bind_tc_ok]
  change (do
    let initializedB' ← v5_cu_probe.good_gate_probe.good_matrices_loop
      directions initialB 0#usize
    let (xorMatrix', xorB') ←
      v5_cu_probe.good_gate_probe.fill_good_base_and_xor_terminals
        initialA initializedB' directionSlice point
    let successor' ←
      v5_cu_probe.good_gate_probe.binary_successor_point point
    v5_cu_probe.good_gate_probe.fill_good_successor_terminal
      xorMatrix' xorB' directionSlice successor') = _
  rw [hinitializeB]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hbaseXor]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [successor_call]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hsuccessorCall]

end GoodMatricesCurrent.SourceExtractedGoodAMatrixOutput
