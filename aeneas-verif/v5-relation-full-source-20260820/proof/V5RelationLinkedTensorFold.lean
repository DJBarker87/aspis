import V5RelationLinkedPreparedSum

/-!
# Exact tensor fold for the linked V5 relation verifier

This file connects the extracted compact tensor branch to the maintained
four-point dual weight fold.  In particular, the proof passes through the
actual prepared-multiplier cache and the actual fused two-product helper.
-/

namespace AspisV5RelationLinkedTensorFold

open Aeneas Aeneas.Std Result
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedFoldArithmetic
open AspisV5RelationLinkedPreparedSum

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev RawPrepared :=
  V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawQM31 :=
  ⟨V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO⟩
local instance : Inhabited RawPrepared :=
  ⟨⟨Array.repeat 3#usize (Array.repeat 3#usize 0#u32)⟩⟩

def CanonicalList (values : List RawQM31) : Prop :=
  ∀ value ∈ values, CanonicalQM31 value

def listCell (values : List RawQM31) (index : Nat) : RawQM31 :=
  (values[index]?).getD default

/-- The four tensor weights in the production bit order. -/
def tensorFibreWeights
    (high low : ExactQM31) : Fin 4 → ExactQM31 :=
  ![1, low, high, high * low]

def tensorDualFactor
    (alpha high low : ExactQM31) : ExactQM31 :=
  AspisV5FriRelationCandidateBridge.dualWeightFoldValue alpha
    (tensorFibreWeights high low)

private theorem vecIndexRun
    (values : alloc.vec.Vec RawQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) values index =
      ok values.val[index.val] := by
  rw [alloc.vec.Vec.index_slice_index]
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec values index hindex)
  simpa [valueEq] using run

private theorem wrappingSubTwoExact
    (length : Std.Usize) (m : Nat)
    (hlength : length.val = m + 2) (hm : m ≤ 8) :
    (Std.Usize.wrapping_sub length 2#usize).val = m := by
  rw [Std.Usize.wrapping_sub_val_eq]
  norm_num
  rw [hlength]
  have hsize : 10 < Std.Usize.size := by
    have h := (11#usize).hSize
    scalar_tac
  have rearrange : m + 2 + (Std.Usize.size - 2) =
      m + Std.Usize.size := by omega
  rw [rearrange, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

private theorem wrappingAddOneExact
    (index : Std.Usize) (m : Nat)
    (hindex : index.val = m) (hm : m ≤ 8) :
    (Std.Usize.wrapping_add index 1#usize).val = m + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  rw [Nat.mod_eq_of_lt, hindex]
  have hsize : 10 < Std.Usize.size := by
    have h := (11#usize).hSize
    scalar_tac
  omega

private theorem oneCanonical :
    CanonicalQM31 V5RelationLinkedGenerated.aspis_core.field.QM31.ONE := by
  norm_num [CanonicalQM31, CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem oneExact :
    toMaintainedExact
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE = 1 := by
  rw [V5RelationLinkedGenerated.aspis_core.field.QM31.ONE]
  rfl

private theorem takeCanonical
    (values : List RawQM31) (m : Nat)
    (canonical : CanonicalList values) :
    CanonicalList (values.take m) := by
  intro value member
  exact canonical value (List.mem_of_mem_take member)

/-- Exact generated tensor component fold.  The last two factors are consumed
as `high` then `low`, the prefix is retained, and the scale is multiplied by
the maintained dual fold of `[1, low, high, high * low]`. -/
theorem extracted_tensor_fold_exact
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (m : Nat)
    (hfactorsLength : factors.val.length = m + 2)
    (hm : m ≤ 8)
    (hscale : CanonicalQM31 scale)
    (hfactors : CanonicalList factors.val)
    (halpha : CanonicalQM31 alpha)
    (halpha2 : CanonicalQM31 alpha2)
    (halpha3 : CanonicalQM31 alpha3)
    (hpreparedAlpha : RepresentsPrepared preparedAlpha alpha)
    (hpreparedAlpha2 : RepresentsPrepared preparedAlpha2 alpha2)
    (halpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (halpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ scaleOut factorsOut,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_tensor_arity4
          scale factors alpha3 preparedAlpha preparedAlpha2 =
        ok (scaleOut, factorsOut) ∧
      CanonicalQM31 scaleOut ∧
      CanonicalList factorsOut.val ∧
      factorsOut.val = factors.val.take m ∧
      toMaintainedExact scaleOut =
        toMaintainedExact scale *
          tensorDualFactor (toMaintainedExact alpha)
            (toMaintainedExact factors.val[m]!)
            (toMaintainedExact factors.val[m + 1]!) := by
  let split := Std.Usize.wrapping_sub (alloc.vec.Vec.len factors) 2#usize
  have hlen : (alloc.vec.Vec.len factors).val = m + 2 := by
    rw [alloc.vec.Vec.len_val]
    exact hfactorsLength
  have hsplit : split.val = m := by
    unfold split
    exact wrappingSubTwoExact (alloc.vec.Vec.len factors) m hlen hm
  let next := Std.Usize.wrapping_add split 1#usize
  have hnext : next.val = m + 1 := by
    unfold next
    exact wrappingAddOneExact split m hsplit hm
  have hsplitBound : split.val < factors.val.length := by omega
  have hnextBound : next.val < factors.val.length := by omega
  have highRead := vecIndexRun factors split hsplitBound
  have lowRead := vecIndexRun factors next hnextBound
  let high := factors.val[split.val]
  let low := factors.val[next.val]
  have highCanonical : CanonicalQM31 high :=
    hfactors high (List.getElem_mem hsplitBound)
  have lowCanonical : CanonicalQM31 low :=
    hfactors low (List.getElem_mem hnextBound)
  have hmBound : m < factors.val.length := by omega
  have hm1Bound : m + 1 < factors.val.length := by omega
  have highBang : high = listCell factors.val m := by
    simp only [high, listCell, hsplit,
      List.getElem?_eq_getElem hmBound, Option.getD_some]
  have lowBang : low = listCell factors.val (m + 1) := by
    simp only [low, listCell, hnext,
      List.getElem?_eq_getElem hm1Bound, Option.getD_some]
  obtain ⟨pqm, pqmRun, pqmRepresents⟩ :=
    generated_prepared_new_establishes low lowCanonical
  obtain ⟨q, qRun, qCanonical, qExact⟩ :=
    generated_prepared_mul_corresponds preparedAlpha alpha high
      hpreparedAlpha halpha highCanonical
  obtain ⟨q1, q1Run, q1Canonical, q1Exact⟩ :=
    generated_qm31_add_corresponds alpha3 q halpha3 qCanonical
  let preparedPair : Array RawPrepared 2#usize :=
    Array.make 2#usize [preparedAlpha2, pqm]
  let leftPair : Array RawQM31 2#usize :=
    Array.make 2#usize [alpha2, low]
  let rightPair : Array RawQM31 2#usize :=
    Array.make 2#usize [high, q1]
  have preparedPairFor : PreparedArrayFor preparedPair leftPair := by
    intro index hindex
    have hi : index = 0 ∨ index = 1 := by omega
    rcases hi with rfl | rfl
    · change PreparedFor preparedAlpha2 alpha2
      exact representsPrepared_implies_preparedFor preparedAlpha2 alpha2
        hpreparedAlpha2 halpha2
    · change PreparedFor pqm low
      exact representsPrepared_implies_preparedFor pqm low pqmRepresents
        lowCanonical
  have rightPairCanonical : CanonicalQM31Array2 rightPair := by
    intro index hindex
    have hi : index = 0 ∨ index = 1 := by omega
    rcases hi with rfl | rfl
    · change CanonicalQM31 high
      exact highCanonical
    · change CanonicalQM31 q1
      exact q1Canonical
  obtain ⟨products, productsRun, productsCanonical, productsExact⟩ :=
    generated_sum_products2_prepared_corresponds preparedPair leftPair
      rightPair preparedPairFor rightPairCanonical
  let one := V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
  obtain ⟨q2, q2Run, q2Canonical, q2Exact⟩ :=
    generated_qm31_add_corresponds one products oneCanonical
      productsCanonical
  obtain ⟨q3, q3Run, q3Canonical, q3Exact⟩ :=
    generated_qm31_half_corresponds q2 q2Canonical
  obtain ⟨factor, factorRun, factorCanonical, factorExact⟩ :=
    generated_qm31_half_corresponds q3 q3Canonical
  obtain ⟨scaleOut, scaleRun, scaleCanonical, scaleExact⟩ :=
    generated_qm31_mul_corresponds scale factor hscale factorCanonical
  let factorsOut : alloc.vec.Vec RawQM31 :=
    ⟨factors.val.take split.val,
      Nat.le_trans (List.length_take_le' ..) factors.property⟩
  refine ⟨scaleOut, factorsOut, ?_, scaleCanonical, ?_, ?_, ?_⟩
  · unfold
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_tensor_arity4
    simp only [Std.lift, bind_tc_ok]
    change (do
      let high1 ← alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) factors split
      let low1 ← alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) factors next
      let pqm1 ←
        V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.new
          low1
      let q1a ←
        V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.mul
          preparedAlpha high1
      let q1b ←
        V5RelationLinkedGenerated.aspis_core.field.QM31.add alpha3 q1a
      let products1 ←
        V5RelationLinkedGenerated.aspis_core.field.qm31_sum_products2_prepared
          (Array.make 2#usize [preparedAlpha2, pqm1])
          (Array.make 2#usize [high1, q1b])
      let q2a ← V5RelationLinkedGenerated.aspis_core.field.QM31.add one products1
      let q3a ← V5RelationLinkedGenerated.aspis_core.field.QM31.half q2a
      let factor1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.half q3a
      let scale1 ←
        V5RelationLinkedGenerated.aspis_core.field.QM31.mul scale factor1
      let factors1 ← alloc.vec.Vec.truncate Global factors split
      ok (scale1, factors1)) = ok (scaleOut, factorsOut)
    rw [highRead, lowRead]
    simp only [bind_tc_ok]
    change (do
      let pqm1 ←
        V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.new
          low
      let q1a ←
        V5RelationLinkedGenerated.aspis_core.field.PreparedQm31Multiplier.mul
          preparedAlpha high
      let q1b ←
        V5RelationLinkedGenerated.aspis_core.field.QM31.add alpha3 q1a
      let products1 ←
        V5RelationLinkedGenerated.aspis_core.field.qm31_sum_products2_prepared
          (Array.make 2#usize [preparedAlpha2, pqm1])
          (Array.make 2#usize [high, q1b])
      let q2a ← V5RelationLinkedGenerated.aspis_core.field.QM31.add one products1
      let q3a ← V5RelationLinkedGenerated.aspis_core.field.QM31.half q2a
      let factor1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.half q3a
      let scale1 ←
        V5RelationLinkedGenerated.aspis_core.field.QM31.mul scale factor1
      let factors1 ← alloc.vec.Vec.truncate Global factors split
      ok (scale1, factors1)) = ok (scaleOut, factorsOut)
    rw [pqmRun]
    simp only [bind_tc_ok]
    rw [qRun]
    simp only [bind_tc_ok]
    rw [q1Run]
    simp only [bind_tc_ok]
    change (do
      let products1 ←
        V5RelationLinkedGenerated.aspis_core.field.qm31_sum_products2_prepared
          preparedPair rightPair
      let q2a ← V5RelationLinkedGenerated.aspis_core.field.QM31.add one products1
      let q3a ← V5RelationLinkedGenerated.aspis_core.field.QM31.half q2a
      let factor1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.half q3a
      let scale1 ←
        V5RelationLinkedGenerated.aspis_core.field.QM31.mul scale factor1
      let factors1 ← alloc.vec.Vec.truncate Global factors split
      ok (scale1, factors1)) = ok (scaleOut, factorsOut)
    rw [productsRun]
    simp only [bind_tc_ok]
    rw [q2Run]
    simp only [bind_tc_ok]
    rw [q3Run]
    simp only [bind_tc_ok]
    rw [factorRun]
    simp only [bind_tc_ok]
    rw [scaleRun]
    rfl
  · unfold factorsOut
    apply takeCanonical factors.val split.val hfactors
  · simp [factorsOut, hsplit]
  · have q1ExactM := congrArg oldQm31ToMaintained q1Exact
    have q2ExactM := congrArg oldQm31ToMaintained q2Exact
    have q3ExactM := congrArg oldQm31ToMaintained q3Exact
    have factorExactM := congrArg oldQm31ToMaintained factorExact
    have scaleExactM := congrArg oldQm31ToMaintained scaleExact
    simp only [oldQm31ToMaintained_toExact,
      oldQm31ToMaintained_add, oldQm31ToMaintained_mul] at q1ExactM q2ExactM q3ExactM factorExactM scaleExactM
    have leftPairVal : leftPair.val = [alpha2, low] := by rfl
    have rightPairVal : rightPair.val = [high, q1] := by rfl
    have productFormula :
        toMaintainedExact products =
          toMaintainedExact alpha2 * toMaintainedExact high +
            toMaintainedExact low * toMaintainedExact q1 := by
      rw [productsExact]
      unfold exactProductDot
      rw [leftPairVal, rightPairVal]
      simp [Finset.sum_range_succ]
    rw [scaleExactM]
    congr 1
    have fourNonzero : (4 : ExactQM31) ≠ 0 := by decide
    apply (eq_div_iff fourNonzero).2
    simp [tensorFibreWeights]
    calc
      toMaintainedExact factor * 4 =
          (toMaintainedExact factor + toMaintainedExact factor) +
            (toMaintainedExact factor + toMaintainedExact factor) := by ring
      _ = toMaintainedExact q3 + toMaintainedExact q3 := by
        rw [factorExactM]
      _ = toMaintainedExact q2 := q3ExactM
      _ = 1 + toMaintainedExact products := by
        rw [q2ExactM, oneExact]
      _ = 1 +
          (toMaintainedExact alpha2 * toMaintainedExact high +
            toMaintainedExact low * toMaintainedExact q1) := by
        rw [productFormula]
      _ = 1 +
          (toMaintainedExact alpha ^ 2 * toMaintainedExact high +
            toMaintainedExact low *
              (toMaintainedExact alpha ^ 3 +
                toMaintainedExact alpha * toMaintainedExact high)) := by
        rw [q1ExactM, qExact, halpha2Exact, halpha3Exact]
      _ = 1 + toMaintainedExact alpha ^ 3 * toMaintainedExact low +
          toMaintainedExact alpha ^ 2 * toMaintainedExact high +
          toMaintainedExact alpha *
            (toMaintainedExact high * toMaintainedExact low) := by ring
      _ = 1 + toMaintainedExact alpha ^ 3 *
              toMaintainedExact (listCell factors.val (m + 1)) +
            toMaintainedExact alpha ^ 2 *
              toMaintainedExact (listCell factors.val m) +
            toMaintainedExact alpha *
              (toMaintainedExact (listCell factors.val m) *
                toMaintainedExact (listCell factors.val (m + 1))) := by
        rw [highBang, lowBang]

#print axioms extracted_tensor_fold_exact

end AspisV5RelationLinkedTensorFold
