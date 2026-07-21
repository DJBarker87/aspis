import ComponentBOptimizedPrimitiveBridge
import SumProductsFullCorrespondence

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace ComponentBRealEvaluatorProof
namespace SumProducts3OperationalAdapterD1E7

private theorem listGetBangEq
    {T : Type} [Inhabited T] (values : List T) (index : Nat)
    (hindex : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem canonicalArrayToCurrent
    {N : Std.Usize} (values : Array QM31 N)
    (canonical : CanonicalArray values) :
    AspisLane5QM31SumProductsProof.CanonicalQM31Array values := by
  intro index hindex
  have h := canonical ⟨index, hindex⟩
  have hbound : index < values.val.length := by
    simpa [Array.length_eq] using hindex
  rw [listGetBangEq values.val index hbound]
  exact h

private theorem generatedArrayIndexRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, hrun, hvalue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have helem := listGetBangEq values.val index.val hbound
  simpa [hvalue, helem] using hrun

/-! The retained Level-3 proof already establishes the fused per-pair helper
against this exact `ComponentBGenerated` extraction.  The lemmas below do not
retarget the wrapper by type coincidence: they replay the current generated
indexed outer-loop body and maintain its channel invariant one source step at
a time. -/

private theorem currentFusedOuterBodyActive
    {N : Std.Usize} (left right : Array QM31 N)
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (index : Std.Usize) (hindex : index.val < N.val)
    (hN : N.val ≤ 4)
    (hleft : AspisLane5QM31SumProductsProof.CanonicalQM31Array left)
    (hright : AspisLane5QM31SumProductsProof.CanonicalQM31Array right)
    (hinvariant : AspisLane5QM31SumProductsProof.OuterChannelInvariant
      current left right index.val) :
    ∃ next out,
      ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop.body
          left right current index = ok (cont (out, next)) ∧
      next.val = index.val + 1 ∧
      AspisLane5QM31SumProductsProof.OuterChannelInvariant
        out left right (index.val + 1) := by
  let ql : QM31 := left.val[index.val]!
  let qr : QM31 := right.val[index.val]!
  have hLeftIndex := generatedArrayIndexRun left index hindex
  have hRightIndex := generatedArrayIndexRun right index hindex
  have hql : AspisLane5QM31SumProductsProof.CanonicalQM31 ql :=
    hleft index.val hindex
  have hqr : AspisLane5QM31SumProductsProof.CanonicalQM31 qr :=
    hright index.val hindex
  have hspace : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (AspisLane5QM31SumProductsProof.matrixCell current row channel).val +
        AspisLane5QM31SumProductsProof.channelProductBound <
          AspisLane5QM31SumProductsProof.u64Cardinality := by
    intro row hrow channel hchannel
    have hbound := (hinvariant row hrow channel hchannel).1
    have hcount : index.val + 1 ≤ 4 := by omega
    calc
      (AspisLane5QM31SumProductsProof.matrixCell current row channel).val +
          AspisLane5QM31SumProductsProof.channelProductBound
          ≤ index.val * AspisLane5QM31SumProductsProof.channelProductBound +
              AspisLane5QM31SumProductsProof.channelProductBound :=
            Nat.add_le_add_right hbound _
      _ = (index.val + 1) *
            AspisLane5QM31SumProductsProof.channelProductBound := by ring
      _ ≤ 4 * AspisLane5QM31SumProductsProof.channelProductBound :=
        Nat.mul_le_mul_right _ hcount
      _ < AspisLane5QM31SumProductsProof.u64Cardinality :=
        AspisLane5QM31SumProductsProof.four_channel_products_fit_u64
  obtain ⟨out, hhelper, hpost⟩ :=
    AspisLane5QM31SumProductsProof.extracted_qm31_accumulate_product_channels_corresponds
      current ql qr hql hqr hspace
  let next := Std.Usize.wrapping_add index 1#usize
  have hnext : next.val = index.val + 1 :=
    AspisLane5QM31SumProductsProof.usize_wrapping_add_one_val_small
      index (by omega)
  have hout : AspisLane5QM31SumProductsProof.OuterChannelInvariant
      out left right (index.val + 1) := by
    intro row hrow channel hchannel
    have hold := hinvariant row hrow channel hchannel
    have hstep := hpost row hrow channel hchannel
    constructor
    · exact le_trans hstep.1 (by
        calc
          (AspisLane5QM31SumProductsProof.matrixCell current row channel).val +
              AspisLane5QM31SumProductsProof.channelProductBound
              ≤ index.val *
                  AspisLane5QM31SumProductsProof.channelProductBound +
                  AspisLane5QM31SumProductsProof.channelProductBound :=
                Nat.add_le_add_right hold.1 _
          _ = (index.val + 1) *
                AspisLane5QM31SumProductsProof.channelProductBound := by ring)
    · rw [hstep.2, hold.2]
      simp [AspisLane5QM31SumProductsProof.exactChannelDot, ql, qr,
        Finset.sum_range_succ]
  refine ⟨next, out, ?_, hnext, hout⟩
  unfold
    ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop.body
  simp only [show index < N from hindex, if_pos]
  rw [hLeftIndex]
  simp only [bind_tc_ok]
  rw [hRightIndex]
  simp only [bind_tc_ok]
  change
    (do
      let sums1 ←
        ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels
          current ql qr
      let index1 ← lift (Std.Usize.wrapping_add index 1#usize)
      ok (cont (sums1, index1))) = ok (cont (out, next))
  rw [hhelper]
  simp only [bind_tc_ok, Std.lift]
  rfl

private theorem currentFusedOuterBodyDone
    {N : Std.Usize} (left right : Array QM31 N)
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (index : Std.Usize) (hdone : ¬ index.val < N.val) :
    ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop.body
        left right current index = ok (done current) := by
  unfold
    ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop.body
  simp [hdone]

private theorem currentFusedOuterLoopCorresponds
    {N : Std.Usize} (left right : Array QM31 N)
    (initial : Array (Array Std.U64 3#usize) 3#usize)
    (hN : N.val ≤ 4)
    (hleft : AspisLane5QM31SumProductsProof.CanonicalQM31Array left)
    (hright : AspisLane5QM31SumProductsProof.CanonicalQM31Array right)
    (hinitial : AspisLane5QM31SumProductsProof.OuterChannelInvariant
      initial left right 0) :
    ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop
        left right initial 0#usize
      ⦃ out => AspisLane5QM31SumProductsProof.OuterChannelInvariant
        out left right N.val ⦄ := by
  simp only [ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop]
  apply loop.spec_decr_nat
    (fun state : Array (Array Std.U64 3#usize) 3#usize × Std.Usize =>
      N.val - state.2.val)
    (fun state => state.2.val ≤ N.val ∧
      AspisLane5QM31SumProductsProof.OuterChannelInvariant
        state.1 left right state.2.val)
    (fun out => AspisLane5QM31SumProductsProof.OuterChannelInvariant
      out left right N.val)
  · rintro ⟨current, index⟩ ⟨hindexLe, hinvariant⟩
    dsimp only at hindexLe hinvariant ⊢
    by_cases hactive : index.val < N.val
    · obtain ⟨next, out, hbody, hnext, hout⟩ :=
        currentFusedOuterBodyActive left right current index hactive hN
          hleft hright hinvariant
      rw [hbody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hnext]
        omega
      · rw [hnext]
        exact hout
      · rw [hnext]
        omega
    · have hatEnd : index.val = N.val := by omega
      rw [currentFusedOuterBodyDone left right current index hactive]
      simpa [hatEnd] using hinvariant
  · exact ⟨by norm_num, hinitial⟩

private theorem reconstructExactEqDot
    {N : Std.Usize} (left right : Array QM31 N)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (hchannels : AspisLane5QM31SumProductsProof.OuterChannelInvariant
      sums left right N.val) :
    AspisLane5QM31SumProductsProof.reconstructQMExact sums =
      AspisLane5QM31SumProductsProof.exactProductDot left right := by
  rw [← AspisLane5QM31SumProductsProof.exact_small_product_sum_eq_dot]
  have h00 := (hchannels 0 (by omega) 0 (by omega)).2
  have h01 := (hchannels 0 (by omega) 1 (by omega)).2
  have h02 := (hchannels 0 (by omega) 2 (by omega)).2
  have h10 := (hchannels 1 (by omega) 0 (by omega)).2
  have h11 := (hchannels 1 (by omega) 1 (by omega)).2
  have h12 := (hchannels 1 (by omega) 2 (by omega)).2
  have h20 := (hchannels 2 (by omega) 0 (by omega)).2
  have h21 := (hchannels 2 (by omega) 1 (by omega)).2
  have h22 := (hchannels 2 (by omega) 2 (by omega)).2
  unfold AspisLane5QM31SumProductsProof.matrixCell at h00 h01 h02 h10 h11 h12 h20 h21 h22
  norm_num at h00 h01 h02 h10 h11 h12 h20 h21 h22
  unfold AspisLane5QM31SumProductsProof.reconstructQMExact
    AspisLane5QM31SumProductsProof.exactSmallProductSum
    AspisLane5QM31SumProductsProof.reconstructCMExact
    AspisLane5QM31SumProductsProof.reconstructExactChannels
  norm_num
  rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  simp

private theorem generatedToExactEqCurrent (value : QM31) :
    generatedQm31ToExact value =
      AspisLane5QM31SumProductsProof.qm31ToExact value := by
  rfl

private theorem currentExactProductDotEqFinSum
    (left right : Array QM31 3#usize) :
    AspisLane5QM31SumProductsProof.exactProductDot left right =
      ∑ index : Fin 3,
        generatedQm31ToExact left.val[index.val] *
          generatedQm31ToExact right.val[index.val] := by
  change
    (∑ index ∈ Finset.range (3#usize).val,
      AspisLane5QM31SumProductsProof.qm31ToExact left.val[index]! *
        AspisLane5QM31SumProductsProof.qm31ToExact right.val[index]!) = _
  norm_num only [UScalar.ofNatCore_val_eq]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ]
  simp [generatedToExactEqCurrent, Fin.sum_univ_succ]
  exact add_assoc _ _ _

/-- Source-clean correspondence for the current owning-crate extraction.  It
uses the retained current-field helper proof, but independently replays the
generated indexed outer loop and reconstruction composition in this module. -/
theorem generated_sumProducts3_operational_correspondence_d1e7 :
    GeneratedSumProducts3Correspondence := by
  intro left right hleft hright
  have hleftCurrent := canonicalArrayToCurrent left hleft
  have hrightCurrent := canonicalArrayToCurrent right hright
  have houterSpec := currentFusedOuterLoopCorresponds left right
    AspisLane5QM31SumProductsProof.zeroU64ChannelMatrix (by norm_num)
    hleftCurrent hrightCurrent
    (AspisLane5QM31SumProductsProof.zero_outer_invariant left right)
  obtain ⟨sums, houter, hchannels⟩ :=
    Aeneas.Std.WP.spec_imp_exists houterSpec
  obtain ⟨out, hreconstruct, hcanonical, hexact⟩ :=
    AspisLane5QM31SumProductsProof.extracted_qm31_from_karatsuba_channel_sums_corresponds
      sums
  refine ⟨out, ?_, hcanonical, ?_⟩
  · unfold ComponentBGenerated.aspis_core.field.qm31_sum_products3
      ComponentBGenerated.aspis_core.field.qm31_sum_products_small
    change
      (do
        let sums1 ←
          ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop
            left right AspisLane5QM31SumProductsProof.zeroU64ChannelMatrix
            0#usize
        ComponentBGenerated.aspis_core.field.qm31_from_karatsuba_channel_sums
          sums1) = ok out
    rw [houter]
    simp only [bind_tc_ok]
    exact hreconstruct
  · rw [generatedToExactEqCurrent, hexact,
      reconstructExactEqDot left right sums hchannels,
      currentExactProductDotEqFinSum left right]

#print axioms generated_sumProducts3_operational_correspondence_d1e7

end SumProducts3OperationalAdapterD1E7
end ComponentBRealEvaluatorProof
