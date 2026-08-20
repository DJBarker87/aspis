import V5RelationLinkedFoldArithmetic

/-!
# Exact production dense-weight fold

This file lifts the exact one-fibre arithmetic theorem to the generated Rust
loop for `WeightComponent::Dense`.  It fixes the source order `4*i+s`, proves
every generated vector read and append, and identifies the resulting vector
with one maintained dual-weight fold layer.
-/

namespace AspisV5RelationLinkedDenseFold

open Aeneas Aeneas.Std Result ControlFlow
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedFoldArithmetic

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawQM31 :=
  ⟨V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO⟩

def CanonicalList (values : List RawQM31) : Prop :=
  ∀ value ∈ values, CanonicalQM31 value

def denseFoldAt
    (values : alloc.vec.Vec RawQM31) (alpha : ExactQM31)
    (fibre : Nat) : ExactQM31 :=
  AspisV5FriRelationCandidateBridge.dualWeightFoldValue alpha
    (fun slot => ![
      toMaintainedExact values.val[4 * fibre]!,
      toMaintainedExact values.val[4 * fibre + 1]!,
      toMaintainedExact values.val[4 * fibre + 2]!,
      toMaintainedExact values.val[4 * fibre + 3]!] slot)

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

private theorem wrapping_mul_four_exact
    (index : Std.Usize)
    (hbound : index.val * 4 < Std.Usize.size) :
    (Std.Usize.wrapping_mul index 4#usize).val = index.val * 4 := by
  rw [Std.Usize.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  simpa using hbound

private theorem getElem_bang_eq
    (values : List RawQM31) (index : Nat)
    (hindex : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem appended_prefix_get
    (xs : List RawQM31) (value : RawQM31) (index : Nat)
    (hindex : index < xs.length) :
    (xs ++ [value])[index]! = xs[index]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
  rw [List.getElem?_append_left hindex]

private theorem appended_last_get
    (xs : List RawQM31) (value : RawQM31) :
    (xs ++ [value])[xs.length]! = value := by
  rw [List.getElem!_eq_getElem?_getD]
  simp

/-- Exact source-extracted dense loop from any already-correct output prefix. -/
theorem extracted_dense_fold_loop_exact
    (values : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31)
    (n k : Nat)
    (hvaluesLength : values.val.length = 4 * n)
    (hn : n ≤ 256)
    (hk : k ≤ n)
    (hvaluesCanonical : CanonicalList values.val)
    (halpha : CanonicalQM31 alpha)
    (halpha2 : CanonicalQM31 alpha2)
    (halpha3 : CanonicalQM31 alpha3)
    (halpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (halpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3)
    (chunkCount : Std.Usize) (hchunkCount : chunkCount.val = n)
    (folded : alloc.vec.Vec RawQM31)
    (hfoldedLength : folded.val.length = k)
    (hfoldedCanonical : CanonicalList folded.val)
    (hfoldedExact : ∀ j, j < k →
      toMaintainedExact folded.val[j]! =
        denseFoldAt values (toMaintainedExact alpha) j)
    (chunkIndex : Std.Usize) (hchunkIndex : chunkIndex.val = k) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4_loop
          values alpha alpha2 alpha3 chunkCount folded chunkIndex = ok out ∧
      out.val.length = n ∧
      CanonicalList out.val ∧
      ∀ j, j < n →
        toMaintainedExact out.val[j]! =
          denseFoldAt values (toMaintainedExact alpha) j := by
  by_cases hmore : k < n
  · have active : chunkIndex < chunkCount := by
      rw [UScalar.lt_equiv, hchunkIndex, hchunkCount]
      exact hmore
    have hsize : 1029 < Std.Usize.size := by
      have h := (1029#usize).hSize
      scalar_tac
    let offset := Std.Usize.wrapping_mul chunkIndex 4#usize
    have hoffset : offset.val = 4 * k := by
      unfold offset
      rw [wrapping_mul_four_exact chunkIndex (by omega), hchunkIndex]
      omega
    let i1 := Std.Usize.wrapping_add offset 1#usize
    let i2 := Std.Usize.wrapping_add offset 2#usize
    let i3 := Std.Usize.wrapping_add offset 3#usize
    have hi1 : i1.val = 4 * k + 1 := by
      unfold i1
      rw [Std.Usize.wrapping_add_val_eq]
      norm_num
      rw [Nat.mod_eq_of_lt (by omega), hoffset]
    have hi2 : i2.val = 4 * k + 2 := by
      unfold i2
      rw [Std.Usize.wrapping_add_val_eq]
      norm_num
      rw [Nat.mod_eq_of_lt (by omega), hoffset]
    have hi3 : i3.val = 4 * k + 3 := by
      unfold i3
      rw [Std.Usize.wrapping_add_val_eq]
      norm_num
      rw [Nat.mod_eq_of_lt (by omega), hoffset]
    have h0 : offset.val < values.val.length := by omega
    have h1 : i1.val < values.val.length := by omega
    have h2 : i2.val < values.val.length := by omega
    have h3 : i3.val < values.val.length := by omega
    have read0 := vec_index_run values offset h0
    have read1 := vec_index_run values i1 h1
    have read2 := vec_index_run values i2 h2
    have read3 := vec_index_run values i3 h3
    have can0 := hvaluesCanonical values.val[offset.val]
      (List.getElem_mem h0)
    have can1 := hvaluesCanonical values.val[i1.val]
      (List.getElem_mem h1)
    have can2 := hvaluesCanonical values.val[i2.val]
      (List.getElem_mem h2)
    have can3 := hvaluesCanonical values.val[i3.val]
      (List.getElem_mem h3)
    obtain ⟨value, foldRun, valueCanonical, valueExactRaw⟩ :=
      linkedFoldFour_corresponds
        values.val[offset.val] values.val[i1.val] values.val[i2.val]
          values.val[i3.val] alpha alpha2 alpha3
        can0 can1 can2 can3 halpha halpha2 halpha3
        halpha2Exact halpha3Exact
    have hcapacity : folded.val.length < Std.Usize.max := by
      rw [hfoldedLength]
      have hmax : 1024 < Std.Usize.max := by
        have h := (1025#usize).hSize
        scalar_tac
      omega
    obtain ⟨foldedNext, pushRun, foldedNextEq⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (alloc.vec.Vec.push_spec folded value hcapacity)
    let chunkIndexNext := Std.Usize.wrapping_add chunkIndex 1#usize
    have hchunkIndexNext : chunkIndexNext.val = k + 1 := by
      unfold chunkIndexNext
      rw [Std.Usize.wrapping_add_val_eq]
      norm_num
      rw [Nat.mod_eq_of_lt (by omega), hchunkIndex]
    have bodyRun :
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4_loop.body
            values alpha alpha2 alpha3 chunkCount folded chunkIndex =
          ok (cont (foldedNext, chunkIndexNext)) := by
      unfold
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4_loop.body
      simp only [Std.lift, bind_tc_ok]
      rw [if_pos active]
      change (do
        let q0 ← alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice RawQM31) values offset
        let q1 ← alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice RawQM31) values i1
        let q2 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul alpha3 q1
        let q3 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add q0 q2
        let q4 ← alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice RawQM31) values i2
        let q5 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul alpha2 q4
        let q6 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add q3 q5
        let q7 ← alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice RawQM31) values i3
        let q8 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul alpha q7
        let q9 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add q6 q8
        let q10 ← V5RelationLinkedGenerated.aspis_core.field.QM31.half q9
        let q11 ← V5RelationLinkedGenerated.aspis_core.field.QM31.half q10
        let folded1 ← alloc.vec.Vec.push folded q11
        let chunkIndex1 ← lift chunkIndexNext
        ok (cont (folded1, chunkIndex1))) =
          ok (cont (foldedNext, chunkIndexNext))
      rw [read0, read1]
      simp only [bind_tc_ok]
      rw [read2]
      simp only [bind_tc_ok]
      rw [read3]
      simp only [bind_tc_ok]
      have combined : (do
          let q11 ← linkedFoldFour
            values.val[offset.val] values.val[i1.val] values.val[i2.val]
              values.val[i3.val] alpha alpha2 alpha3
          let folded1 ← alloc.vec.Vec.push folded q11
          let chunkIndex1 ← lift chunkIndexNext
          ok (cont (folded1, chunkIndex1))) =
            (ok (cont (foldedNext, chunkIndexNext)) :
              Result (ControlFlow
                ((alloc.vec.Vec RawQM31) × Std.Usize)
                (alloc.vec.Vec RawQM31))) := by
        rw [foldRun]
        simp only [bind_tc_ok]
        rw [pushRun]
        simp only [bind_tc_ok]
        rfl
      simpa only [linkedFoldFour, Aeneas.Std.lift,
        Aeneas.Std.bind_assoc_eq] using combined
    have hfoldedNextLength : foldedNext.val.length = k + 1 := by
      rw [foldedNextEq, List.length_append]
      simp [hfoldedLength]
    have hfoldedNextCanonical : CanonicalList foldedNext.val := by
      intro x hx
      rw [foldedNextEq] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hfoldedCanonical x hx
      · have hxEq : x = value := List.mem_singleton.mp hx
        subst x
        simpa using valueCanonical
    have valueExact :
        toMaintainedExact value =
          denseFoldAt values (toMaintainedExact alpha) k := by
      simpa [denseFoldAt, hoffset, hi1, hi2, hi3,
        getElem_bang_eq values.val (4 * k) (by omega),
        getElem_bang_eq values.val (4 * k + 1) (by omega),
        getElem_bang_eq values.val (4 * k + 2) (by omega),
        getElem_bang_eq values.val (4 * k + 3) (by omega)] using valueExactRaw
    have hfoldedNextExact : ∀ j, j < k + 1 →
        toMaintainedExact foldedNext.val[j]! =
          denseFoldAt values (toMaintainedExact alpha) j := by
      intro j hj
      rw [foldedNextEq]
      by_cases hjk : j < k
      · rw [appended_prefix_get folded.val value j (by omega)]
        exact hfoldedExact j hjk
      · have hjEq : j = k := by omega
        subst j
        have last := appended_last_get folded.val value
        rw [hfoldedLength] at last
        rw [last]
        exact valueExact
    rw [V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4_loop,
      Aeneas.Std.loop.eq_1]
    simp only
    rw [bodyRun]
    simp only
    obtain ⟨out, outRun, outLength, outCanonical, outExact⟩ :=
      extracted_dense_fold_loop_exact values alpha alpha2 alpha3 n (k + 1)
        hvaluesLength hn (by omega) hvaluesCanonical halpha halpha2 halpha3
        halpha2Exact halpha3Exact chunkCount hchunkCount foldedNext
        hfoldedNextLength hfoldedNextCanonical hfoldedNextExact
        chunkIndexNext hchunkIndexNext
    have outRun' :
        Aeneas.Std.loop
          (fun state =>
            V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4_loop.body
              values alpha alpha2 alpha3 chunkCount state.1 state.2)
          (foldedNext, chunkIndexNext) = ok out := by
      simpa only [
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4_loop]
        using outRun
    rw [outRun']
    exact ⟨out, rfl, outLength, outCanonical, outExact⟩
  · have hkEq : k = n := by omega
    have inactive : ¬ chunkIndex < chunkCount := by
      rw [UScalar.lt_equiv, hchunkIndex, hchunkCount]
      omega
    have bodyRun :
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4_loop.body
            values alpha alpha2 alpha3 chunkCount folded chunkIndex =
          ok (done folded) := by
      unfold
        V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4_loop.body
      simp only [Std.lift, bind_tc_ok]
      rw [if_neg inactive]
    rw [V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4_loop,
      Aeneas.Std.loop.eq_1]
    simp only
    rw [bodyRun]
    exact ⟨folded, rfl, by omega, hfoldedCanonical, fun j hj =>
      hfoldedExact j (by omega)⟩
termination_by n - k
decreasing_by omega

private theorem emptyVecCanonical (capacity : Std.Usize) :
    CanonicalList
      (alloc.vec.Vec.with_capacity RawQM31 capacity).val := by
  intro value hvalue
  simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] at hvalue

/-- The generated dense entrypoint computes the exact quotient, starts from
the empty vector, and returns precisely one maintained dual fold per fibre. -/
theorem extracted_dense_fold_exact
    (values : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31)
    (n : Nat)
    (hvaluesLength : values.val.length = 4 * n)
    (hn : n ≤ 256)
    (hvaluesCanonical : CanonicalList values.val)
    (halpha : CanonicalQM31 alpha)
    (halpha2 : CanonicalQM31 alpha2)
    (halpha3 : CanonicalQM31 alpha3)
    (halpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (halpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4
          values alpha alpha2 alpha3 = ok out ∧
      out.val.length = n ∧
      CanonicalList out.val ∧
      ∀ j, j < n →
        toMaintainedExact out.val[j]! =
          denseFoldAt values (toMaintainedExact alpha) j := by
  obtain ⟨chunkCount, divRun, chunkCountValue⟩ :=
    UScalar.div_spec values.len (y := 4#usize) (by norm_num)
  have hchunkCount : chunkCount.val = n := by
    have exact := chunkCountValue
    simp only [Slice.len_val] at exact
    norm_num at exact
    rw [hvaluesLength] at exact
    omega
  let empty := alloc.vec.Vec.with_capacity RawQM31 chunkCount
  have hemptyLength : empty.val.length = 0 := by rfl
  have hemptyExact : ∀ j, j < 0 →
      toMaintainedExact empty.val[j]! =
        denseFoldAt values (toMaintainedExact alpha) j := by
    intro j hj
    omega
  obtain ⟨out, loopRun, outLength, outCanonical, outExact⟩ :=
    extracted_dense_fold_loop_exact values alpha alpha2 alpha3 n 0
      hvaluesLength hn (by omega) hvaluesCanonical halpha halpha2 halpha3
      halpha2Exact halpha3Exact chunkCount hchunkCount empty hemptyLength
      (emptyVecCanonical chunkCount) hemptyExact 0#usize (by rfl)
  refine ⟨out, ?_, outLength, outCanonical, outExact⟩
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.WeightAccumulator.fold_dense_arity4
  simp only
  rw [divRun]
  simpa only [bind_tc_ok, empty] using loopRun

#print axioms extracted_dense_fold_loop_exact
#print axioms extracted_dense_fold_exact

end AspisV5RelationLinkedDenseFold
