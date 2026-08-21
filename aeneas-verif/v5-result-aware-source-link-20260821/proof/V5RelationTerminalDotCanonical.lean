import V5RelationUnconditionalCanonical
import V5RelationLinkedWeightPath
import V5AcceptedRelationRoundInversion

/-!
# Canonical outputs from the exact production terminal dots

The terminal main dot may contain arbitrary stored weight representatives.
That does not prevent a representation proof: every multiplication reduces
its output, and every subsequent addition receives canonical operands.  The
lemmas below follow the exact linked `WeightAccumulator.dot` loops used by the
accepted relation verifier.
-/

namespace AspisV5RelationTerminalDotCanonical

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5RelationUnconditionalCanonical
open AspisV5AcceptedRelationRoundInversion

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev CanonicalQM31 :=
  AspisV5RelationGeneratedFieldProjection.CanonicalQM31

deriving instance Inhabited for V5RelationLinkedGenerated.aspis_core.field.CM31
deriving instance Inhabited for V5RelationLinkedGenerated.aspis_core.field.QM31
deriving instance Inhabited for V5RelationCompactFinalGenerated.aspis_core.field.M31
deriving instance Inhabited for V5RelationCompactFinalGenerated.aspis_core.field.CM31
deriving instance Inhabited for V5RelationCompactFinalGenerated.aspis_core.field.QM31

def CanonicalSlice (values : Slice RawQM31) : Prop :=
  ∀ index, index < values.val.length → CanonicalQM31 values.val[index]!

private theorem linked_qm31_zero_canonical :
    CanonicalQM31 V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO := by
  norm_num [V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    CanonicalQM31,
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
    AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem slice_index_run
    (values : Slice RawQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    Slice.index_usize values index = .ok values.val[index.val]! := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq]
  simp [hindex]

private theorem wrapping_succ_exact
    (values : Slice RawQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hlength := Slice.length_ineq values
  change index.val + 1 < UScalar.size .Usize
  rw [UScalar.size_UScalarTyUsize]
  have hsize := Usize.size_scalarTac_eq
  omega

private theorem array_index_run
    {T : Type} [Inhabited T] {count : Std.Usize}
    (values : Array T count) (index : Std.Usize)
    (hindex : index.val < count.val) :
    Array.index_usize values index = .ok values.val[index.val]! := by
  obtain ⟨value, run, valueExact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have listBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have getExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simp
  simpa [valueExact, getExact] using run

private theorem iterator_some_advances
    {T : Type} (iter nextIter : core.slice.iter.Iter T) (value : T)
    (run : core.slice.iter.IteratorSliceIter.next iter =
      .ok (some value, nextIter)) :
    iter.i < iter.slice.val.length ∧ nextIter.slice = iter.slice ∧
      nextIter.i = iter.i + 1 := by
  unfold core.slice.iter.IteratorSliceIter.next at run
  split at run
  next active =>
    simp only [Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at run
    cases run.2
    exact ⟨by scalar_tac, rfl, rfl⟩
  next inactive => simp at run

/-- Success of the direct dense component loop preserves canonicality of its
running sum.  Weight values need no representation premise. -/
private theorem dense_dot_loop_success_canonical
    (values : Slice RawQM31)
    (weights : alloc.vec.Vec RawQM31)
    (sum : RawQM31) (index : Std.Usize) (out : RawQM31)
    (hvalues : CanonicalSlice values) (hsum : CanonicalQM31 sum)
    (run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop0
          values weights sum index = .ok out) :
    CanonicalQM31 out := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop0
    at run
  rw [Aeneas.Std.loop.eq_def] at run
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop0.body
    at run
  simp only [] at run
  by_cases hactive : index.val < values.val.length
  · have hactiveScalar : index < Slice.len values := by scalar_tac
    rw [if_pos hactiveScalar] at run
    rw [slice_index_run values index hactive] at run
    simp only [bind_tc_ok] at run
    generalize hweight :
        alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice RawQM31) weights index =
          weightResult at run
    cases weightResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
    | div => simp [Bind.bind, Aeneas.Std.bind] at run
    | ok weight =>
        simp only [bind_tc_ok] at run
        generalize hproduct :
            V5RelationLinkedGenerated.aspis_core.field.QM31.mul
              values.val[index.val]! weight = productResult at run
        cases productResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
        | div => simp [Bind.bind, Aeneas.Std.bind] at run
        | ok product =>
            have hproductCanonical :=
              linked_qm31_mul_success_canonical_any
                values.val[index.val]! weight product hproduct
            simp only [bind_tc_ok] at run
            generalize hnextSum :
                V5RelationLinkedGenerated.aspis_core.field.QM31.add
                  sum product = nextSumResult at run
            cases nextSumResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
            | div => simp [Bind.bind, Aeneas.Std.bind] at run
            | ok nextSum =>
                have hnextCanonical := linked_qm31_add_success_canonical
                  sum product nextSum hsum hproductCanonical hnextSum
                simp only [bind_tc_ok, Aeneas.Std.lift] at run
                have hnextIndex := wrapping_succ_exact values index hactive
                exact dense_dot_loop_success_canonical values weights nextSum
                  (Std.Usize.wrapping_add index 1#usize) out hvalues
                  hnextCanonical run
  · have hinactiveScalar : ¬ index < Slice.len values := by scalar_tac
    rw [if_neg hinactiveScalar] at run
    simp only [Result.ok.injEq] at run
    subst out
    exact hsum
termination_by values.val.length - index.val
decreasing_by
  rw [hnextIndex]
  omega

/-- The released deferred-group component uses a row-to-group lookup before
the same multiply/add recurrence.  Successful lookup is enough; the selected
weight itself need not be canonical. -/
private theorem grouped_dot_loop_success_canonical
    (values : Slice RawQM31)
    (rowGroups : alloc.vec.Vec Std.U8)
    (groupValues : alloc.vec.Vec RawQM31)
    (sum : RawQM31) (index : Std.Usize) (out : RawQM31)
    (hvalues : CanonicalSlice values) (hsum : CanonicalQM31 sum)
    (run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop1
          values rowGroups groupValues sum index = .ok out) :
    CanonicalQM31 out := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop1
    at run
  rw [Aeneas.Std.loop.eq_def] at run
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop1.body
    at run
  simp only [] at run
  by_cases hactive : index.val < values.val.length
  · have hactiveScalar : index < Slice.len values := by scalar_tac
    rw [if_pos hactiveScalar] at run
    rw [slice_index_run values index hactive] at run
    simp only [bind_tc_ok] at run
    generalize hrow :
        alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice Std.U8) rowGroups index =
          rowResult at run
    cases rowResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
    | div => simp [Bind.bind, Aeneas.Std.bind] at run
    | ok row =>
        simp only [bind_tc_ok, Aeneas.Std.lift] at run
        generalize hweight :
            alloc.vec.Vec.index
              (core.slice.index.SliceIndexUsizeSlice RawQM31) groupValues
              (core.convert.num.FromUsizeU8.from row) = weightResult at run
        cases weightResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
        | div => simp [Bind.bind, Aeneas.Std.bind] at run
        | ok weight =>
            simp only [bind_tc_ok] at run
            generalize hproduct :
                V5RelationLinkedGenerated.aspis_core.field.QM31.mul
                  values.val[index.val]! weight = productResult at run
            cases productResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
            | div => simp [Bind.bind, Aeneas.Std.bind] at run
            | ok product =>
                have hproductCanonical :=
                  linked_qm31_mul_success_canonical_any
                    values.val[index.val]! weight product hproduct
                simp only [bind_tc_ok] at run
                generalize hnextSum :
                    V5RelationLinkedGenerated.aspis_core.field.QM31.add
                      sum product = nextSumResult at run
                cases nextSumResult with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                | div => simp [Bind.bind, Aeneas.Std.bind] at run
                | ok nextSum =>
                    have hnextCanonical := linked_qm31_add_success_canonical
                      sum product nextSum hsum hproductCanonical hnextSum
                    simp only [bind_tc_ok, Aeneas.Std.lift] at run
                    have hnextIndex := wrapping_succ_exact values index hactive
                    exact grouped_dot_loop_success_canonical values rowGroups
                      groupValues nextSum (Std.Usize.wrapping_add index 1#usize)
                      out hvalues hnextCanonical run
  · have hinactiveScalar : ¬ index < Slice.len values := by scalar_tac
    rw [if_neg hinactiveScalar] at run
    simp only [Result.ok.injEq] at run
    subst out
    exact hsum
termination_by values.val.length - index.val
decreasing_by
  rw [hnextIndex]
  omega

/-- One successful invocation of the exact component-loop body either ends at
the unchanged total or advances one slot with another canonical total. -/
private theorem direct_dot_body_success_shape
    (iter : core.slice.iter.Iter
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightComponent)
    (values : Slice RawQM31) (total : RawQM31)
    (flow : ControlFlow
      ((core.slice.iter.Iter
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightComponent) × RawQM31)
      RawQM31)
    (hlen : values.val.length = 4)
    (hvalues : CanonicalSlice values) (htotal : CanonicalQM31 total)
    (run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
        values iter total = .ok flow) :
    flow = .done total ∨
      ∃ nextIter nextTotal,
        flow = .cont (nextIter, nextTotal) ∧
        iter.i < iter.slice.val.length ∧
        nextIter.slice = iter.slice ∧ nextIter.i = iter.i + 1 ∧
        CanonicalQM31 nextTotal := by
  have h0 : 0 < values.val.length := by omega
  have h1 : 1 < values.val.length := by omega
  have h2 : 2 < values.val.length := by omega
  have h3 : 3 < values.val.length := by omega
  have read0 := slice_index_run values 0#usize h0
  have read1 := slice_index_run values 1#usize h1
  have read2 := slice_index_run values 2#usize h2
  have read3 := slice_index_run values 3#usize h3
  have canon0 := hvalues 0 h0
  have canon1 := hvalues 1 h1
  have canon2 := hvalues 2 h2
  have canon3 := hvalues 3 h3
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
    at run
  dsimp only at run
  generalize hnext : core.slice.iter.IteratorSliceIter.next iter = nextResult at run
  cases nextResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok pair =>
      rcases pair with ⟨component?, nextIter⟩
      simp only [bind_tc_ok] at run
      cases component? with
      | none =>
          dsimp only at run
          simp only [Result.ok.injEq] at run
          exact Or.inl run.symm
      | some component =>
          have advance := iterator_some_advances iter nextIter component hnext
          cases component with
          | Geometric scale base =>
              dsimp only at run
              obtain ⟨base2, base2Run, base2Canonical⟩ :=
                linked_qm31_square_exists_canonical_any base
              obtain ⟨term1, term1Run, term1Canonical⟩ :=
                linked_qm31_mul_exists_canonical_any base
                  values.val[(1#usize).val]!
              obtain ⟨sum1, sum1Run, sum1Canonical⟩ :=
                linked_qm31_add_exists_canonical
                  values.val[(0#usize).val]! term1
                  (by simpa using canon0) term1Canonical
              obtain ⟨term2, term2Run, term2Canonical⟩ :=
                linked_qm31_mul_exists_canonical_any base2
                  values.val[(2#usize).val]!
              obtain ⟨sum2, sum2Run, sum2Canonical⟩ :=
                linked_qm31_add_exists_canonical sum1 term2
                  sum1Canonical term2Canonical
              obtain ⟨base3, base3Run, base3Canonical⟩ :=
                linked_qm31_mul_exists_canonical_any base2 base
              obtain ⟨term3, term3Run, term3Canonical⟩ :=
                linked_qm31_mul_exists_canonical_any base3
                  values.val[(3#usize).val]!
              obtain ⟨evaluation, evaluationRun, evaluationCanonical⟩ :=
                linked_qm31_add_exists_canonical sum2 term3
                  sum2Canonical term3Canonical
              obtain ⟨contribution, contributionRun, contributionCanonical⟩ :=
                linked_qm31_mul_exists_canonical_any scale evaluation
              obtain ⟨nextTotal, nextTotalRun, nextTotalCanonical⟩ :=
                linked_qm31_add_exists_canonical total contribution
                  htotal contributionCanonical
              simp only [base2Run, read0, read1, term1Run, sum1Run, read2,
                term2Run, sum2Run, base3Run, read3, term3Run,
                evaluationRun, contributionRun, nextTotalRun, bind_tc_ok] at run
              simp only [Result.ok.injEq] at run
              subst flow
              exact Or.inr ⟨nextIter, nextTotal, rfl, advance.1,
                advance.2.1, advance.2.2, nextTotalCanonical⟩
          | Multilinear scale point =>
              dsimp only at run
              generalize hpoint1 :
                  alloc.vec.Vec.index
                    (core.slice.index.SliceIndexUsizeSlice RawQM31)
                    point 1#usize = point1Result at run
              cases point1Result with
              | fail error => simp [read0, Bind.bind, Aeneas.Std.bind] at run
              | div => simp [read0, Bind.bind, Aeneas.Std.bind] at run
              | ok point1 =>
                  simp only [bind_tc_ok] at run
                  obtain ⟨lowDelta, lowDeltaRun, lowDeltaCanonical⟩ :=
                    linked_qm31_sub_exists_canonical
                      values.val[(1#usize).val]!
                      values.val[(0#usize).val]!
                      (by simpa using canon1) (by simpa using canon0)
                  obtain ⟨lowTerm, lowTermRun, lowTermCanonical⟩ :=
                    linked_qm31_mul_exists_canonical_any point1 lowDelta
                  obtain ⟨low, lowRun, lowCanonical⟩ :=
                    linked_qm31_add_exists_canonical
                      values.val[(0#usize).val]! lowTerm
                      (by simpa using canon0) lowTermCanonical
                  obtain ⟨highDelta, highDeltaRun, highDeltaCanonical⟩ :=
                    linked_qm31_sub_exists_canonical
                      values.val[(3#usize).val]!
                      values.val[(2#usize).val]!
                      (by simpa using canon3) (by simpa using canon2)
                  obtain ⟨highTerm, highTermRun, highTermCanonical⟩ :=
                    linked_qm31_mul_exists_canonical_any point1 highDelta
                  obtain ⟨high, highRun, highCanonical⟩ :=
                    linked_qm31_add_exists_canonical
                      values.val[(2#usize).val]! highTerm
                      (by simpa using canon2) highTermCanonical
                  simp only [read0, read1, lowDeltaRun, lowTermRun, lowRun,
                    read2, read3, highDeltaRun, highTermRun, highRun,
                    bind_tc_ok] at run
                  generalize hpoint0 :
                      alloc.vec.Vec.index
                        (core.slice.index.SliceIndexUsizeSlice RawQM31)
                        point 0#usize = point0Result at run
                  cases point0Result with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                  | div => simp [Bind.bind, Aeneas.Std.bind] at run
                  | ok point0 =>
                      obtain ⟨outerDelta, outerDeltaRun, outerDeltaCanonical⟩ :=
                        linked_qm31_sub_exists_canonical high low highCanonical
                          lowCanonical
                      obtain ⟨outerTerm, outerTermRun, outerTermCanonical⟩ :=
                        linked_qm31_mul_exists_canonical_any point0 outerDelta
                      obtain ⟨evaluation, evaluationRun, evaluationCanonical⟩ :=
                        linked_qm31_add_exists_canonical low outerTerm
                          lowCanonical outerTermCanonical
                      obtain ⟨contribution, contributionRun,
                          contributionCanonical⟩ :=
                        linked_qm31_mul_exists_canonical_any scale evaluation
                      obtain ⟨nextTotal, nextTotalRun, nextTotalCanonical⟩ :=
                        linked_qm31_add_exists_canonical total contribution
                          htotal contributionCanonical
                      simp only [outerDeltaRun, outerTermRun, evaluationRun,
                        contributionRun,
                        nextTotalRun, bind_tc_ok] at run
                      simp only [Result.ok.injEq] at run
                      subst flow
                      exact Or.inr ⟨nextIter, nextTotal, rfl, advance.1,
                        advance.2.1, advance.2.2, nextTotalCanonical⟩
          | Tensor scale factors =>
              dsimp only at run
              generalize hfactor1 :
                  alloc.vec.Vec.index
                    (core.slice.index.SliceIndexUsizeSlice RawQM31)
                    factors 1#usize = factor1Result at run
              cases factor1Result with
              | fail error => simp [read0, Bind.bind, Aeneas.Std.bind] at run
              | div => simp [read0, Bind.bind, Aeneas.Std.bind] at run
              | ok factor1 =>
                  obtain ⟨lowTerm, lowTermRun, lowTermCanonical⟩ :=
                    linked_qm31_mul_exists_canonical_any factor1
                      values.val[(1#usize).val]!
                  obtain ⟨low, lowRun, lowCanonical⟩ :=
                    linked_qm31_add_exists_canonical
                      values.val[(0#usize).val]! lowTerm
                      (by simpa using canon0) lowTermCanonical
                  obtain ⟨highTerm, highTermRun, highTermCanonical⟩ :=
                    linked_qm31_mul_exists_canonical_any factor1
                      values.val[(3#usize).val]!
                  obtain ⟨high, highRun, highCanonical⟩ :=
                    linked_qm31_add_exists_canonical
                      values.val[(2#usize).val]! highTerm
                      (by simpa using canon2) highTermCanonical
                  simp only [read0, read1, lowTermRun, lowRun, read2,
                    read3, highTermRun, highRun, bind_tc_ok] at run
                  generalize hfactor0 :
                      alloc.vec.Vec.index
                        (core.slice.index.SliceIndexUsizeSlice RawQM31)
                        factors 0#usize = factor0Result at run
                  cases factor0Result with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                  | div => simp [Bind.bind, Aeneas.Std.bind] at run
                  | ok factor0 =>
                      obtain ⟨outerTerm, outerTermRun, outerTermCanonical⟩ :=
                        linked_qm31_mul_exists_canonical_any factor0 high
                      obtain ⟨evaluation, evaluationRun, evaluationCanonical⟩ :=
                        linked_qm31_add_exists_canonical low outerTerm
                          lowCanonical outerTermCanonical
                      obtain ⟨contribution, contributionRun,
                          contributionCanonical⟩ :=
                        linked_qm31_mul_exists_canonical_any scale evaluation
                      obtain ⟨nextTotal, nextTotalRun, nextTotalCanonical⟩ :=
                        linked_qm31_add_exists_canonical total contribution
                          htotal contributionCanonical
                      simp only [outerTermRun, evaluationRun, contributionRun,
                        nextTotalRun, bind_tc_ok] at run
                      simp only [Result.ok.injEq] at run
                      subst flow
                      exact Or.inr ⟨nextIter, nextTotal, rfl, advance.1,
                        advance.2.1, advance.2.2, nextTotalCanonical⟩
          | Product scale pairs =>
              dsimp only at run
              generalize hpair0 :
                  alloc.vec.Vec.index
                    (core.slice.index.SliceIndexUsizeSlice
                      (Array RawQM31 2#usize)) pairs 0#usize =
                    pair0Result at run
              cases pair0Result with
              | fail error => simp [read0, Bind.bind, Aeneas.Std.bind] at run
              | div => simp [read0, Bind.bind, Aeneas.Std.bind] at run
              | ok pair0 =>
                  have pair0Read0 := array_index_run pair0 0#usize (by norm_num)
                  have pair0Read1 := array_index_run pair0 1#usize (by norm_num)
                  simp only [read0, pair0Read0, pair0Read1, bind_tc_ok] at run
                  generalize hpair1 :
                      alloc.vec.Vec.index
                        (core.slice.index.SliceIndexUsizeSlice
                          (Array RawQM31 2#usize)) pairs 1#usize =
                        pair1Result at run
                  cases pair1Result with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                  | div => simp [Bind.bind, Aeneas.Std.bind] at run
                  | ok pair1 =>
                      have pair1Read0 :=
                        array_index_run pair1 0#usize (by norm_num)
                      have pair1Read1 :=
                        array_index_run pair1 1#usize (by norm_num)
                      obtain ⟨factor00, factor00Run, factor00Canonical⟩ :=
                        linked_qm31_mul_exists_canonical_any
                          pair0.val[(0#usize).val]!
                          pair1.val[(0#usize).val]!
                      obtain ⟨term0, term0Run, term0Canonical⟩ :=
                        linked_qm31_mul_exists_canonical_any
                          values.val[(0#usize).val]! factor00
                      obtain ⟨factor01, factor01Run, factor01Canonical⟩ :=
                        linked_qm31_mul_exists_canonical_any
                          pair0.val[(0#usize).val]!
                          pair1.val[(1#usize).val]!
                      obtain ⟨term1, term1Run, term1Canonical⟩ :=
                        linked_qm31_mul_exists_canonical_any
                          values.val[(1#usize).val]! factor01
                      obtain ⟨sum01, sum01Run, sum01Canonical⟩ :=
                        linked_qm31_add_exists_canonical term0 term1
                          term0Canonical term1Canonical
                      obtain ⟨factor10, factor10Run, factor10Canonical⟩ :=
                        linked_qm31_mul_exists_canonical_any
                          pair0.val[(1#usize).val]!
                          pair1.val[(0#usize).val]!
                      obtain ⟨term2, term2Run, term2Canonical⟩ :=
                        linked_qm31_mul_exists_canonical_any
                          values.val[(2#usize).val]! factor10
                      obtain ⟨sum012, sum012Run, sum012Canonical⟩ :=
                        linked_qm31_add_exists_canonical sum01 term2
                          sum01Canonical term2Canonical
                      obtain ⟨factor11, factor11Run, factor11Canonical⟩ :=
                        linked_qm31_mul_exists_canonical_any
                          pair0.val[(1#usize).val]!
                          pair1.val[(1#usize).val]!
                      obtain ⟨term3, term3Run, term3Canonical⟩ :=
                        linked_qm31_mul_exists_canonical_any
                          values.val[(3#usize).val]! factor11
                      obtain ⟨evaluation, evaluationRun, evaluationCanonical⟩ :=
                        linked_qm31_add_exists_canonical sum012 term3
                          sum012Canonical term3Canonical
                      obtain ⟨contribution, contributionRun,
                          contributionCanonical⟩ :=
                        linked_qm31_mul_exists_canonical_any scale evaluation
                      obtain ⟨nextTotal, nextTotalRun, nextTotalCanonical⟩ :=
                        linked_qm31_add_exists_canonical total contribution
                          htotal contributionCanonical
                      simp only [pair1Read0, pair1Read1, factor00Run,
                        term0Run, read1, factor01Run, term1Run, sum01Run,
                        read2, factor10Run, term2Run, sum012Run, read3,
                        factor11Run, term3Run, evaluationRun, contributionRun,
                        nextTotalRun, bind_tc_ok] at run
                      simp only [Result.ok.injEq] at run
                      subst flow
                      exact Or.inr ⟨nextIter, nextTotal, rfl, advance.1,
                        advance.2.1, advance.2.2, nextTotalCanonical⟩
          | Dense weights =>
              dsimp only at run
              generalize hcontribution :
                  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop0
                    values weights
                    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
                    0#usize = contributionResult at run
              cases contributionResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
              | div => simp [Bind.bind, Aeneas.Std.bind] at run
              | ok contribution =>
                  have contributionCanonical :=
                    dense_dot_loop_success_canonical values weights
                      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
                      0#usize contribution hvalues
                      linked_qm31_zero_canonical
                      hcontribution
                  obtain ⟨nextTotal, nextTotalRun, nextTotalCanonical⟩ :=
                    linked_qm31_add_exists_canonical total contribution
                      htotal contributionCanonical
                  simp only [nextTotalRun, bind_tc_ok, Result.ok.injEq] at run
                  subst flow
                  exact Or.inr ⟨nextIter, nextTotal, rfl, advance.1,
                    advance.2.1, advance.2.2, nextTotalCanonical⟩
          | Grouped64x16 rowGroups groupValues groupCount =>
              simp [Bind.bind, Aeneas.Std.bind] at run
          | Grouped64x16BinaryDeferred rowGroups groupIds maybeGroup groupValues =>
              dsimp only at run
              generalize hcontribution :
                  V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0_loop1
                    values rowGroups groupValues
                    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
                    0#usize = contributionResult at run
              cases contributionResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
              | div => simp [Bind.bind, Aeneas.Std.bind] at run
              | ok contribution =>
                  have contributionCanonical :=
                    grouped_dot_loop_success_canonical values rowGroups
                      groupValues
                      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
                      0#usize contribution hvalues
                      linked_qm31_zero_canonical
                      hcontribution
                  obtain ⟨nextTotal, nextTotalRun, nextTotalCanonical⟩ :=
                    linked_qm31_add_exists_canonical total contribution
                      htotal contributionCanonical
                  simp only [nextTotalRun, bind_tc_ok, Result.ok.injEq] at run
                  subst flow
                  exact Or.inr ⟨nextIter, nextTotal, rfl, advance.1,
                    advance.2.1, advance.2.2, nextTotalCanonical⟩
          | Grouped128x16 rowGroups groupValues groupCount =>
              simp [Bind.bind, Aeneas.Std.bind] at run

/-- The exact fast-path component loop preserves canonicality.  The four
released values must be canonical; stored weights and component parameters
may use arbitrary raw representatives because every multiplication and square
reduces its result before it reaches an addition. -/
private theorem direct_dot_loop_success_canonical
    (iter : core.slice.iter.Iter
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightComponent)
    (values : Slice RawQM31) (total out : RawQM31)
    (hlen : values.val.length = 4)
    (hvalues : CanonicalSlice values) (htotal : CanonicalQM31 total)
    (run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0
        iter values total = .ok out) :
    CanonicalQM31 out := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0
    at run
  rw [Aeneas.Std.loop.eq_def] at run
  dsimp only at run
  generalize hbody :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0.body
        values iter total = bodyResult at run
  cases bodyResult with
  | fail error =>
      simp at run
  | div =>
      simp at run
  | ok flow =>
      rcases direct_dot_body_success_shape iter values total flow hlen hvalues
        htotal hbody with ended | continued
      · subst flow
        simp only [Result.ok.injEq] at run
        subst out
        exact htotal
      · obtain ⟨nextIter, nextTotal, flowExact, active, sameSlice,
          nextIndex, nextCanonical⟩ := continued
        subst flow
        simp only [bind_tc_ok] at run
        change
          V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot_loop0
            nextIter values nextTotal = .ok out at run
        exact direct_dot_loop_success_canonical nextIter values nextTotal out
          hlen hvalues nextCanonical run
termination_by iter.slice.val.length - iter.i
decreasing_by
  rw [sameSlice, nextIndex]
  omega

/-- At the released terminal shape, successful execution of the exact linked
production dot returns a canonical field representative. -/
theorem linked_released_dot_success_canonical
    (weights :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator)
    (values : Array RawQM31 4#usize) (out : RawQM31)
    (logLength : weights.log_len = 2#u32)
    (hvalues : ∀ index, index < 4 → CanonicalQM31 values.val[index]!)
    (run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.dot
        weights (Array.to_slice values) = .ok out) :
    CanonicalQM31 out := by
  rw [AspisV5RelationLinkedWeightPath.released_terminal_array_uses_direct_components
    weights values logLength] at run
  generalize hiter :
      SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
        Global weights.components = iterResult at run
  cases iterResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok iter =>
      simp only [bind_tc_ok] at run
      have sliceLength : (Array.to_slice values).val.length = 4 := by
        simpa [Array.to_slice] using values.property
      have sliceCanonical : CanonicalSlice (Array.to_slice values) := by
        intro index indexBound
        apply hvalues index
        omega
      exact direct_dot_loop_success_canonical iter (Array.to_slice values)
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO out sliceLength
        sliceCanonical linked_qm31_zero_canonical run

/-- The full verifier extraction delegates its terminal main dot to the exact
linked extraction.  A successful released-shape call therefore has the same
canonical-output guarantee. -/
theorem full_released_dot_success_canonical
    (weights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (values : Array RawQM31 4#usize) (out : RawQM31)
    (logLength : weights.log_len = 2#u32)
    (hvalues : ∀ index, index < 4 → CanonicalQM31 values.val[index]!)
    (run :
      aspis_core.sumcheck.WeightAccumulator.dot
        weights (Array.to_slice values) = .ok out) :
    CanonicalQM31 out := by
  unfold aspis_core.sumcheck.WeightAccumulator.dot at run
  apply linked_released_dot_success_canonical _ values out
    (by
      change weights.log_len = 2#u32
      exact logLength) hvalues run

/-- The full verifier's extracted fold has the same exact two-bit log-length
decrement as the production-linked extraction to which it delegates. -/
theorem full_fold_success_decrements_log_length
    (weights output :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (alpha : RawQM31)
    (run :
      aspis_core.sumcheck.WeightAccumulator.fold weights alpha = .ok output) :
    output.log_len = Std.U32.wrapping_sub weights.log_len 2#u32 := by
  unfold aspis_core.sumcheck.WeightAccumulator.fold at run
  generalize linkedRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold
        _ alpha = linkedResult at run
  cases linkedResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok linkedOutput =>
      simp only [bind_tc_ok, Result.ok.injEq] at run
      subst output
      have exactLog :=
        AspisV5RelationLinkedWeightPath.fold_success_decrements_log_length
          _ linkedOutput alpha linkedRun
      change
        linkedOutput.log_len =
          Std.U32.wrapping_sub weights.log_len 2#u32
      change
        linkedOutput.log_len =
          Std.U32.wrapping_sub
            (V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.log_len
              _) 2#u32 at exactLog
      exact exactLog

/-- Four successful full-verifier folds from the released ten-bit domain
reach the exact four-value terminal domain. -/
theorem four_full_folds_end_at_log_two
    (weights0 weights1 weights2 weights3 weights4 :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (alpha0 alpha1 alpha2 alpha3 : RawQM31)
    (initialLog : weights0.log_len = 10#u32)
    (fold0 : aspis_core.sumcheck.WeightAccumulator.fold weights0 alpha0 =
      .ok weights1)
    (fold1 : aspis_core.sumcheck.WeightAccumulator.fold weights1 alpha1 =
      .ok weights2)
    (fold2 : aspis_core.sumcheck.WeightAccumulator.fold weights2 alpha2 =
      .ok weights3)
    (fold3 : aspis_core.sumcheck.WeightAccumulator.fold weights3 alpha3 =
      .ok weights4) :
    weights4.log_len = 2#u32 := by
  have log1 := full_fold_success_decrements_log_length
    weights0 weights1 alpha0 fold0
  have log2 := full_fold_success_decrements_log_length
    weights1 weights2 alpha1 fold1
  have log3 := full_fold_success_decrements_log_length
    weights2 weights3 alpha2 fold2
  have log4 := full_fold_success_decrements_log_length
    weights3 weights4 alpha3 fold3
  have tenToEight : Std.U32.wrapping_sub 10#u32 2#u32 = 8#u32 := by decide
  have eightToSix : Std.U32.wrapping_sub 8#u32 2#u32 = 6#u32 := by decide
  have sixToFour : Std.U32.wrapping_sub 6#u32 2#u32 = 4#u32 := by decide
  have fourToTwo : Std.U32.wrapping_sub 4#u32 2#u32 = 2#u32 := by decide
  rw [initialLog, tenToEight] at log1
  rw [log1, eightToSix] at log2
  rw [log2, sixToFour] at log3
  rw [log3, fourToTwo] at log4
  exact log4

/-- The four fold calls recovered from one accepted outer execution end at
the released four-value terminal shape once its prepared starting domain is
identified as the fixed ten-bit domain. -/
theorem accepted_trace_weights4_log_two_of_initial
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace :
      AspisV5RelationAcceptanceSourceProof.AcceptedMode9FullRelationTrace
        parsed finalPolynomial alphas kappa inactiveClaim roundChallenges
        preparedClaims terminalClaim)
    (initialLog : trace.calls.relation.weights.log_len = 10#u32) :
    trace.weights4.log_len = 2#u32 := by
  obtain ⟨rounds⟩ := accepted_full_trace_exposes_four_round_executions trace
  have log1 := full_fold_success_decrements_log_length
    rounds.round0.weights2 trace.weights1 (acceptedAlphaAt alphas 0)
    rounds.round0.polynomial.scalar.weightFoldRun
  have log2 := full_fold_success_decrements_log_length
    rounds.round1.weights2 trace.weights2 (acceptedAlphaAt alphas 1)
    rounds.round1.polynomial.scalar.weightFoldRun
  have log3 := full_fold_success_decrements_log_length
    rounds.round2.weights2 trace.weights3 (acceptedAlphaAt alphas 2)
    rounds.round2.polynomial.scalar.weightFoldRun
  have log4 := full_fold_success_decrements_log_length
    rounds.round3.weights2 trace.weights4 (acceptedAlphaAt alphas 3)
    rounds.round3.polynomial.scalar.weightFoldRun
  rw [rounds.round0.sample1WeightLog, rounds.round0.sample0WeightLog] at log1
  rw [rounds.round1.sample1WeightLog, rounds.round1.sample0WeightLog] at log2
  rw [rounds.round2.sample1WeightLog, rounds.round2.sample0WeightLog] at log3
  rw [rounds.round3.sample1WeightLog, rounds.round3.sample0WeightLog] at log4
  have tenToEight : Std.U32.wrapping_sub 10#u32 2#u32 = 8#u32 := by decide
  have eightToSix : Std.U32.wrapping_sub 8#u32 2#u32 = 6#u32 := by decide
  have sixToFour : Std.U32.wrapping_sub 6#u32 2#u32 = 4#u32 := by decide
  have fourToTwo : Std.U32.wrapping_sub 4#u32 2#u32 = 2#u32 := by decide
  rw [initialLog, tenToEight] at log1
  rw [log1, eightToSix] at log2
  rw [log2, sixToFour] at log3
  rw [log3, fourToTwo] at log4
  exact log4

/-- The main terminal dot from one accepted execution is canonical.  This
uses the exact same-run four folds, the exact final coefficient array, and
the successful production dot call retained by the accepted trace. -/
theorem accepted_trace_main_dot_canonical_of_initial
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace :
      AspisV5RelationAcceptanceSourceProof.AcceptedMode9FullRelationTrace
        parsed finalPolynomial alphas kappa inactiveClaim roundChallenges
        preparedClaims terminalClaim)
    (initialLog : trace.calls.relation.weights.log_len = 10#u32)
    (finalCanonical : ∀ index, index < 4 →
      CanonicalQM31 trace.finalCoefficients.val[index]!) :
    CanonicalQM31 trace.mainDot := by
  apply full_released_dot_success_canonical trace.weights4
    trace.finalCoefficients trace.mainDot
  · exact accepted_trace_weights4_log_two_of_initial trace initialLog
  · exact finalCanonical
  · exact trace.mainDotSuccess

/-- The exact four-term terminal dot maintained by the compact additive state
returns a canonical representative whenever it succeeds.  Stored terminal
weights and supplied values may have arbitrary raw representatives: every
multiplication reduces before its result enters the addition chain. -/
theorem compact_additive_dot_success_canonical
    (state : V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights)
    (values : Array RawQM31 4#usize) (out : RawQM31)
    (run :
      V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive.dot
        state values = .ok out) :
    CanonicalQM31 out := by
  unfold
    V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive.dot
    at run
  generalize finalWeightsRun :
      V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights
        _ = finalWeightsResult at run
  cases finalWeightsResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok weights =>
    simp only [bind_tc_ok] at run
    rw [array_index_run weights 0#usize (by decide),
      array_index_run weights 1#usize (by decide),
      array_index_run weights 2#usize (by decide),
      array_index_run weights 3#usize (by decide),
      array_index_run values 0#usize (by decide),
      array_index_run values 1#usize (by decide),
      array_index_run values 2#usize (by decide),
      array_index_run values 3#usize (by decide)] at run
    simp only [bind_tc_ok] at run
    generalize product0Run :
        V5RelationFullGenerated.aspis_core.field.QM31.mul _ _ =
          product0Result at run
    cases product0Result with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
    | div => simp [Bind.bind, Aeneas.Std.bind] at run
    | ok product0 =>
      simp only [bind_tc_ok] at run
      have product0Canonical := generated_qm31_mul_success_canonical_any
        _ _ product0 product0Run
      generalize sum0Run :
          V5RelationFullGenerated.aspis_core.field.QM31.add
            V5RelationFullGenerated.aspis_core.field.QM31.ZERO product0 =
              sum0Result at run
      cases sum0Result with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok sum0 =>
        simp only [bind_tc_ok] at run
        have sum0Canonical := generated_qm31_add_success_canonical
          _ product0 sum0 generated_qm31_zero_canonical product0Canonical
          sum0Run
        generalize product1Run :
            V5RelationFullGenerated.aspis_core.field.QM31.mul _ _ =
              product1Result at run
        cases product1Result with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
        | div => simp [Bind.bind, Aeneas.Std.bind] at run
        | ok product1 =>
          simp only [bind_tc_ok] at run
          have product1Canonical := generated_qm31_mul_success_canonical_any
            _ _ product1 product1Run
          generalize sum1Run :
              V5RelationFullGenerated.aspis_core.field.QM31.add
                sum0 product1 = sum1Result at run
          cases sum1Result with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
          | div => simp [Bind.bind, Aeneas.Std.bind] at run
          | ok sum1 =>
            simp only [bind_tc_ok] at run
            have sum1Canonical := generated_qm31_add_success_canonical
              sum0 product1 sum1 sum0Canonical product1Canonical sum1Run
            generalize product2Run :
                V5RelationFullGenerated.aspis_core.field.QM31.mul _ _ =
                  product2Result at run
            cases product2Result with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
            | div => simp [Bind.bind, Aeneas.Std.bind] at run
            | ok product2 =>
              simp only [bind_tc_ok] at run
              have product2Canonical :=
                generated_qm31_mul_success_canonical_any _ _ product2
                  product2Run
              generalize sum2Run :
                  V5RelationFullGenerated.aspis_core.field.QM31.add
                    sum1 product2 = sum2Result at run
              cases sum2Result with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
              | div => simp [Bind.bind, Aeneas.Std.bind] at run
              | ok sum2 =>
                simp only [bind_tc_ok] at run
                have sum2Canonical := generated_qm31_add_success_canonical
                  sum1 product2 sum2 sum1Canonical product2Canonical sum2Run
                generalize product3Run :
                    V5RelationFullGenerated.aspis_core.field.QM31.mul _ _ =
                      product3Result at run
                cases product3Result with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                | div => simp [Bind.bind, Aeneas.Std.bind] at run
                | ok product3 =>
                  simp only [bind_tc_ok] at run
                  have product3Canonical :=
                    generated_qm31_mul_success_canonical_any _ _ product3
                      product3Run
                  exact generated_qm31_add_success_canonical sum2 product3 out
                    sum2Canonical product3Canonical run

/-- The additive terminal value retained by one accepted outer execution is
canonical by direct execution of its translated Rust dot. -/
theorem accepted_trace_additive_dot_canonical
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace :
      AspisV5RelationAcceptanceSourceProof.AcceptedMode9FullRelationTrace
        parsed finalPolynomial alphas kappa inactiveClaim roundChallenges
        preparedClaims terminalClaim) :
    CanonicalQM31 trace.additiveDot :=
  compact_additive_dot_success_canonical trace.additive4
    trace.finalCoefficients trace.additiveDot trace.additiveDotSuccess

/-- The accepted terminal equality is the exact field equality used by the
maintained relation verifier, with both dot representations discharged from
the same translated Rust execution. -/
theorem accepted_trace_terminal_add_exact_of_initial
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace :
      AspisV5RelationAcceptanceSourceProof.AcceptedMode9FullRelationTrace
        parsed finalPolynomial alphas kappa inactiveClaim roundChallenges
        preparedClaims terminalClaim)
    (initialLog : trace.calls.relation.weights.log_len = 10#u32)
    (finalCanonical : ∀ index, index < 4 →
      CanonicalQM31 trace.finalCoefficients.val[index]!) :
    AspisV5AcceptedRelationRoundProjection.toField trace.mainDot +
        AspisV5AcceptedRelationRoundProjection.toField trace.additiveDot =
      AspisV5AcceptedRelationRoundProjection.toField trace.claim4 := by
  exact accepted_terminal_add_is_exact trace
    (accepted_trace_main_dot_canonical_of_initial trace initialLog
      finalCanonical)
    (accepted_trace_additive_dot_canonical trace)

#print axioms dense_dot_loop_success_canonical
#print axioms grouped_dot_loop_success_canonical
#print axioms direct_dot_loop_success_canonical
#print axioms linked_released_dot_success_canonical
#print axioms full_released_dot_success_canonical
#print axioms full_fold_success_decrements_log_length
#print axioms four_full_folds_end_at_log_two
#print axioms accepted_trace_weights4_log_two_of_initial
#print axioms accepted_trace_main_dot_canonical_of_initial
#print axioms compact_additive_dot_success_canonical
#print axioms accepted_trace_additive_dot_canonical
#print axioms accepted_trace_terminal_add_exact_of_initial

end AspisV5RelationTerminalDotCanonical
