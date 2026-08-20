import V5RelationLinkedDenseFold

/-!
# Exact structured V5 weight folds

The production accumulator keeps some covectors in compact multilinear or
tensor form.  This file starts the source-to-model proof for those compact
arms with the complete generated multilinear helper.
-/

namespace AspisV5RelationLinkedStructuredFold

open Aeneas Aeneas.Std Result
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedFoldArithmetic

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawQM31 :=
  ⟨V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO⟩

def CanonicalList (values : List RawQM31) : Prop :=
  ∀ value ∈ values, CanonicalQM31 value

def multilinearFibreWeights
    (z0 z1 : ExactQM31) : Fin 4 → ExactQM31 :=
  ![(1 - z0) * (1 - z1),
    (1 - z0) * z1,
    z0 * (1 - z1),
    z0 * z1]

def multilinearDualFactor
    (alpha z0 z1 : ExactQM31) : ExactQM31 :=
  AspisV5FriRelationCandidateBridge.dualWeightFoldValue alpha
    (multilinearFibreWeights z0 z1)

private theorem vec_index_run
    (values : alloc.vec.Vec RawQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) values index =
      ok values.val[index.val] := by
  rw [alloc.vec.Vec.index_slice_index]
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec values index hindex)
  simpa [valueEq] using run

private theorem wrapping_sub_two_exact
    (length : Std.Usize) (m : Nat)
    (hlength : length.val = m + 2)
    (hm : m ≤ 8) :
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

private theorem wrapping_add_one_exact
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

/-- Exact generated multilinear component fold.  The last two point
coordinates are consumed in the production bit order, the prefix is retained,
and the scale is multiplied by precisely the maintained dual fold of the four
multilinear basis weights. -/
theorem extracted_multilinear_fold_exact
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31) (m : Nat)
    (hpointLength : point.val.length = m + 2)
    (hm : m ≤ 8)
    (hscale : CanonicalQM31 scale)
    (hpoint : CanonicalList point.val)
    (halpha : CanonicalQM31 alpha)
    (halpha2 : CanonicalQM31 alpha2)
    (halpha3 : CanonicalQM31 alpha3)
    (halpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (halpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ scaleOut pointOut,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
          scale point alpha alpha2 alpha3 = ok (scaleOut, pointOut) ∧
      CanonicalQM31 scaleOut ∧
      CanonicalList pointOut.val ∧
      pointOut.val = point.val.take m ∧
      toMaintainedExact scaleOut =
        toMaintainedExact scale *
          multilinearDualFactor (toMaintainedExact alpha)
            (toMaintainedExact point.val[m]!)
            (toMaintainedExact point.val[m + 1]!) := by
  let split := Std.Usize.wrapping_sub (alloc.vec.Vec.len point) 2#usize
  have hlen : (alloc.vec.Vec.len point).val = m + 2 := by
    rw [alloc.vec.Vec.len_val]
    exact hpointLength
  have hsplit : split.val = m := by
    unfold split
    exact wrapping_sub_two_exact (alloc.vec.Vec.len point) m hlen hm
  let next := Std.Usize.wrapping_add split 1#usize
  have hnext : next.val = m + 1 := by
    unfold next
    exact wrapping_add_one_exact split m hsplit hm
  have hsplitBound : split.val < point.val.length := by omega
  have hnextBound : next.val < point.val.length := by omega
  have read0 := vec_index_run point split hsplitBound
  have read1 := vec_index_run point next hnextBound
  have z0Canonical := hpoint point.val[split.val]
    (List.getElem_mem hsplitBound)
  have z1Canonical := hpoint point.val[next.val]
    (List.getElem_mem hnextBound)
  let one := V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
  obtain ⟨q, qRun, qCanonical, qExact⟩ :=
    generated_qm31_sub_corresponds alpha3 one halpha3 oneCanonical
  obtain ⟨q1, q1Run, q1Canonical, q1Exact⟩ :=
    generated_qm31_mul_corresponds q point.val[next.val]
      qCanonical z1Canonical
  obtain ⟨low, lowRun, lowCanonical, lowExact⟩ :=
    generated_qm31_add_corresponds one q1 oneCanonical q1Canonical
  obtain ⟨q2, q2Run, q2Canonical, q2Exact⟩ :=
    generated_qm31_sub_corresponds alpha alpha2 halpha halpha2
  obtain ⟨q3, q3Run, q3Canonical, q3Exact⟩ :=
    generated_qm31_mul_corresponds q2 point.val[next.val]
      q2Canonical z1Canonical
  obtain ⟨high, highRun, highCanonical, highExact⟩ :=
    generated_qm31_add_corresponds alpha2 q3 halpha2 q3Canonical
  obtain ⟨q4, q4Run, q4Canonical, q4Exact⟩ :=
    generated_qm31_sub_corresponds high low highCanonical lowCanonical
  obtain ⟨q5, q5Run, q5Canonical, q5Exact⟩ :=
    generated_qm31_mul_corresponds point.val[split.val] q4
      z0Canonical q4Canonical
  obtain ⟨q6, q6Run, q6Canonical, q6Exact⟩ :=
    generated_qm31_add_corresponds low q5 lowCanonical q5Canonical
  obtain ⟨q7, q7Run, q7Canonical, q7Exact⟩ :=
    generated_qm31_half_corresponds q6 q6Canonical
  obtain ⟨factor, factorRun, factorCanonical, factorExact⟩ :=
    generated_qm31_half_corresponds q7 q7Canonical
  obtain ⟨scaleOut, scaleRun, scaleCanonical, scaleExact⟩ :=
    generated_qm31_mul_corresponds scale factor hscale factorCanonical
  let pointOut : alloc.vec.Vec RawQM31 :=
    ⟨point.val.take split.val,
      Nat.le_trans (List.length_take_le' ..) point.property⟩
  refine ⟨scaleOut, pointOut, ?_, scaleCanonical, ?_, ?_, ?_⟩
  · unfold
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_multilinear_arity4
    simp only [Std.lift, bind_tc_ok]
    change (do
      let z0 ← alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) point split
      let z1 ← alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) point next
      let q ← V5RelationLinkedGenerated.aspis_core.field.QM31.sub alpha3 one
      let q1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul q z1
      let low ← V5RelationLinkedGenerated.aspis_core.field.QM31.add one q1
      let q2 ← V5RelationLinkedGenerated.aspis_core.field.QM31.sub alpha alpha2
      let q3 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul q2 z1
      let high ← V5RelationLinkedGenerated.aspis_core.field.QM31.add alpha2 q3
      let q4 ← V5RelationLinkedGenerated.aspis_core.field.QM31.sub high low
      let q5 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul z0 q4
      let q6 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add low q5
      let q7 ← V5RelationLinkedGenerated.aspis_core.field.QM31.half q6
      let factor ← V5RelationLinkedGenerated.aspis_core.field.QM31.half q7
      let scale1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul scale factor
      let point1 ← alloc.vec.Vec.truncate Global point split
      ok (scale1, point1)) = ok (scaleOut, pointOut)
    rw [read0, read1]
    simp only [bind_tc_ok]
    rw [qRun]
    simp only [bind_tc_ok]
    rw [q1Run]
    simp only [bind_tc_ok]
    rw [lowRun]
    simp only [bind_tc_ok]
    rw [q2Run]
    simp only [bind_tc_ok]
    rw [q3Run]
    simp only [bind_tc_ok]
    rw [highRun]
    simp only [bind_tc_ok]
    rw [q4Run]
    simp only [bind_tc_ok]
    rw [q5Run]
    simp only [bind_tc_ok]
    rw [q6Run]
    simp only [bind_tc_ok]
    rw [q7Run]
    simp only [bind_tc_ok]
    rw [factorRun]
    simp only [bind_tc_ok]
    rw [scaleRun]
    rfl
  · unfold pointOut
    apply takeCanonical point.val split.val hpoint
  · simp [pointOut, hsplit]
  · have qExactM := congrArg oldQm31ToMaintained qExact
    have q1ExactM := congrArg oldQm31ToMaintained q1Exact
    have lowExactM := congrArg oldQm31ToMaintained lowExact
    have q2ExactM := congrArg oldQm31ToMaintained q2Exact
    have q3ExactM := congrArg oldQm31ToMaintained q3Exact
    have highExactM := congrArg oldQm31ToMaintained highExact
    have q4ExactM := congrArg oldQm31ToMaintained q4Exact
    have q5ExactM := congrArg oldQm31ToMaintained q5Exact
    have q6ExactM := congrArg oldQm31ToMaintained q6Exact
    have q7ExactM := congrArg oldQm31ToMaintained q7Exact
    have factorExactM := congrArg oldQm31ToMaintained factorExact
    have scaleExactM := congrArg oldQm31ToMaintained scaleExact
    simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add,
      oldQm31ToMaintained_sub, oldQm31ToMaintained_mul] at qExactM q1ExactM lowExactM q2ExactM q3ExactM highExactM
    simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add,
      oldQm31ToMaintained_sub, oldQm31ToMaintained_mul] at q4ExactM q5ExactM q6ExactM q7ExactM factorExactM scaleExactM
    rw [scaleExactM]
    congr 1
    have fourNonzero : (4 : ExactQM31) ≠ 0 := by decide
    apply (eq_div_iff fourNonzero).2
    simp [multilinearFibreWeights]
    calc
      toMaintainedExact factor * 4 =
          (toMaintainedExact factor + toMaintainedExact factor) +
            (toMaintainedExact factor + toMaintainedExact factor) := by ring
      _ = toMaintainedExact q7 + toMaintainedExact q7 := by
        rw [factorExactM]
      _ = toMaintainedExact q6 := q7ExactM
      _ = toMaintainedExact low + toMaintainedExact q5 := q6ExactM
      _ = toMaintainedExact low +
          toMaintainedExact point.val[split.val] * toMaintainedExact q4 := by
        rw [q5ExactM]
      _ = toMaintainedExact low +
          toMaintainedExact point.val[split.val] *
            (toMaintainedExact high - toMaintainedExact low) := by
        rw [q4ExactM]
      _ = (1 + (toMaintainedExact alpha ^ 3 - 1) *
              toMaintainedExact point.val[next.val]) +
          toMaintainedExact point.val[split.val] *
            ((toMaintainedExact alpha ^ 2 +
                (toMaintainedExact alpha - toMaintainedExact alpha ^ 2) *
                  toMaintainedExact point.val[next.val]) -
              (1 + (toMaintainedExact alpha ^ 3 - 1) *
                toMaintainedExact point.val[next.val])) := by
        rw [lowExactM, q1ExactM, qExactM, highExactM, q3ExactM,
          q2ExactM, oneExact, halpha2Exact, halpha3Exact]
      _ =
          (1 - toMaintainedExact ((point.val[m]?).getD default)) *
              (1 - toMaintainedExact ((point.val[m + 1]?).getD default)) +
            toMaintainedExact alpha ^ 3 *
              ((1 - toMaintainedExact ((point.val[m]?).getD default)) *
                toMaintainedExact ((point.val[m + 1]?).getD default)) +
            toMaintainedExact alpha ^ 2 *
              (toMaintainedExact ((point.val[m]?).getD default) *
                (1 - toMaintainedExact ((point.val[m + 1]?).getD default))) +
            toMaintainedExact alpha *
              (toMaintainedExact ((point.val[m]?).getD default) *
                toMaintainedExact ((point.val[m + 1]?).getD default)) := by
        have hmBound : m < point.val.length := by omega
        have hm1Bound : m + 1 < point.val.length := by omega
        have splitGetD : (point.val[m]?).getD default =
            point.val[split.val] := by
          rw [List.getElem?_eq_getElem hmBound, Option.getD_some]
          simp only [hsplit]
        have nextGetD : (point.val[m + 1]?).getD default =
            point.val[next.val] := by
          rw [List.getElem?_eq_getElem hm1Bound, Option.getD_some]
          simp only [hnext]
        rw [splitGetD, nextGetD]
        ring

#print axioms extracted_multilinear_fold_exact

end AspisV5RelationLinkedStructuredFold
