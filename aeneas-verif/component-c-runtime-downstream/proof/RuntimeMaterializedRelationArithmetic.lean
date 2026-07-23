import RuntimeFoldPrimitiveInstantiation
import ComponentCRuntimeGenerated
import AspisFormal.V5ComponentCRelationRowLinearity

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow
open scoped BigOperators

namespace aspis_prover.ComponentCRuntimeMaterializedRelationArithmetic

open aspis_prover
open ComponentCRuntimeFoldPrimitiveInstantiation

abbrev RawQM31 := aspis_core.field.QM31

local instance : Inhabited RawQM31 := ⟨aspis_core.field.QM31.ZERO⟩

def RuntimeCanonicalList (values : List RawQM31) : Prop :=
  ∀ value ∈ values, runtimeCanonicalQM31 value

def exactSliceEntry (values : Slice RawQM31) (index : Nat) : ExactQM31 :=
  runtimeQM31View values.val[index]!

private theorem raw_zero_canonical :
    runtimeCanonicalQM31 aspis_core.field.QM31.ZERO := by
  norm_num [runtimeCanonicalQM31, runtimeCanonicalCM31, runtimeCanonicalM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    aspis_core.field.QM31.ZERO]

private theorem raw_zero_exact :
    runtimeQM31View aspis_core.field.QM31.ZERO = (0 : ExactQM31) := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      simp [runtimeQM31View, runtimeCM31View, aspis_core.field.QM31.ZERO]
  · apply QuadraticAlgebra.ext <;>
      simp [runtimeQM31View, runtimeCM31View, aspis_core.field.QM31.ZERO]

private theorem raw_quarter_canonical :
    runtimeCanonicalM31 aspis_core.field.M31_QUARTER := by
  norm_num [runtimeCanonicalM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    aspis_core.field.M31_QUARTER]

private theorem raw_quarter_exact :
    runtimeM31View aspis_core.field.M31_QUARTER = (4 : ExactQM31)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simp only [runtimeM31View, aspis_core.field.M31_QUARTER]
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · change (536870912 : ExactM31) * 4 = 1
      decide
    · change (536870912 : ExactM31) * 0 = 0
      ring
  · apply QuadraticAlgebra.ext
    · change (0 : ExactM31) * 4 = 0
      ring
    · change (0 : ExactM31) * 0 = 0
      ring

private theorem slice_index_run
    (values : Slice RawQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    Slice.index_usize values index = ok values.val[index.val] := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq]
  simp [hindex]

private theorem wrapping_succ_exact
    (index : Std.Usize) (hindex : index.val < 1024) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  have hone : (1#usize : Std.Usize).val = 1 := rfl
  rw [hone]
  apply Nat.mod_eq_of_lt
  have room : 1025 < UScalar.size .Usize := by
    have h := (1025#usize).hSize
    scalar_tac
  omega

private theorem wrapping_add_exact
    (left right : Std.Usize)
    (hsum : left.val + right.val < UScalar.size .Usize) :
    (Std.Usize.wrapping_add left right).val = left.val + right.val := by
  rw [Std.Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt hsum]

private theorem exactSliceEntry_eq
    (values : Slice RawQM31) (index : Nat)
    (hindex : index < values.val.length) :
    exactSliceEntry values index = runtimeQM31View values.val[index] := by
  unfold exactSliceEntry
  congr 1
  apply List.getElem!_of_getElem?
  simp [hindex]

/-- The source-extracted materialized dot loop is the exact ordered inner
product.  This is universal in the two canonical slices and is the arithmetic
core used by every Component-C OOD release. -/
theorem extracted_materialized_dot_loop_exact
    (coefficients table : Slice RawQM31)
    (hlen : coefficients.val.length = table.val.length)
    (hbound : coefficients.val.length ≤ 1024)
    (hcoefficients : RuntimeCanonicalList coefficients.val)
    (htable : RuntimeCanonicalList table.val)
    (total : RawQM31) (htotal : runtimeCanonicalQM31 total)
    (index : Std.Usize) (hindex : index.val ≤ coefficients.val.length) :
    ∃ out,
      v5_mask.relation_prover.V5IncrementalRelation.materialized_dot_loop
          coefficients table total index = ok out ∧
      runtimeCanonicalQM31 out ∧
      runtimeQM31View out = runtimeQM31View total +
        ∑ row ∈ Finset.Ico index.val coefficients.val.length,
          exactSliceEntry coefficients row * exactSliceEntry table row := by
  unfold v5_mask.relation_prover.V5IncrementalRelation.materialized_dot_loop
  by_cases more : index.val < coefficients.val.length
  · have moreScalar : index < coefficients.len := by
      simpa [Slice.len_val] using more
    have coefficientRead := slice_index_run coefficients index more
    have tableBound : index.val < table.val.length := by omega
    have tableRead := slice_index_run table index tableBound
    have coefficientCanonical := hcoefficients coefficients.val[index.val]
      (List.getElem_mem more)
    have tableCanonical := htable table.val[index.val]
      (List.getElem_mem tableBound)
    obtain ⟨product, productRun, productCanonical, productExact⟩ :=
      runtime_qm31_mul_corresponds coefficients.val[index.val]
        table.val[index.val] coefficientCanonical tableCanonical
    obtain ⟨nextTotal, addRun, nextCanonical, nextExact⟩ :=
      runtime_qm31_add_corresponds total product htotal productCanonical
    let nextIndex := Std.Usize.wrapping_add index 1#usize
    have nextIndexValue : nextIndex.val = index.val + 1 := by
      apply wrapping_succ_exact index
      omega
    have nextBound : nextIndex.val ≤ coefficients.val.length := by omega
    have hbody :
        v5_mask.relation_prover.V5IncrementalRelation.materialized_dot_loop.body
            coefficients table total index = ok (cont (nextTotal, nextIndex)) := by
      unfold v5_mask.relation_prover.V5IncrementalRelation.materialized_dot_loop.body
      rw [if_pos moreScalar, coefficientRead, tableRead]
      simp only [bind_tc_ok]
      change
        (do
          let product ← aspis_core.field.QM31.mul
            coefficients.val[index.val] table.val[index.val]
          let next ← aspis_core.field.QM31.add total product
          let nextIndex' ← lift (Std.Usize.wrapping_add index 1#usize)
          ok (cont (next, nextIndex'))) = ok (cont (nextTotal, nextIndex))
      rw [productRun]
      simp only [bind_tc_ok]
      rw [addRun]
      rfl
    rw [loop.eq_1]
    simp only [Prod.fst, Prod.snd]
    rw [hbody]
    simp only [bind_tc_ok]
    obtain ⟨out, loopRun, outCanonical, outExact⟩ :=
      extracted_materialized_dot_loop_exact coefficients table hlen hbound
        hcoefficients htable nextTotal nextCanonical nextIndex nextBound
    have loopRun' :
        loop
            (fun state =>
              v5_mask.relation_prover.V5IncrementalRelation.materialized_dot_loop.body
                coefficients table state.1 state.2)
            (nextTotal, nextIndex) = ok out := by
      simpa only [
        v5_mask.relation_prover.V5IncrementalRelation.materialized_dot_loop]
        using loopRun
    rw [loopRun']
    refine ⟨out, rfl, outCanonical, ?_⟩
    rw [outExact, nextExact, productExact, nextIndexValue]
    simp only [exactSliceEntry]
    have coefficientBang :
        coefficients.val[index.val]! = coefficients.val[index.val] := by
      apply List.getElem!_of_getElem?
      simp [more]
      rfl
    have tableBang : table.val[index.val]! = table.val[index.val] := by
      apply List.getElem!_of_getElem?
      simp [tableBound]
    let summand := fun row : Nat =>
      runtimeQM31View coefficients.val[row]! * runtimeQM31View table.val[row]!
    have split := Finset.sum_Ico_consecutive summand
      (Nat.le_succ index.val) (show index.val + 1 ≤ coefficients.val.length by omega)
    have singleton :
        ∑ row ∈ Finset.Ico index.val (index.val + 1), summand row =
          summand index.val := by
      rw [Finset.sum_Ico_succ_top (Nat.le_refl index.val)]
      simp
    rw [← split, singleton]
    dsimp only [summand]
    rw [coefficientBang, tableBang]
    ring
  · have hDone : index.val = coefficients.val.length := by omega
    have doneScalar : ¬ index < coefficients.len := by
      simpa [Slice.len_val, hDone]
    have hbody :
        v5_mask.relation_prover.V5IncrementalRelation.materialized_dot_loop.body
            coefficients table total index = ok (done total) := by
      unfold v5_mask.relation_prover.V5IncrementalRelation.materialized_dot_loop.body
      rw [if_neg doneScalar]
    rw [loop.eq_1]
    simp only [Prod.fst, Prod.snd]
    rw [hbody]
    refine ⟨total, rfl, htotal, ?_⟩
    simp [hDone]
termination_by coefficients.val.length - index.val
decreasing_by
  rw [nextIndexValue]
  omega

/-- The public source function starts the exact loop from zero. -/
theorem extracted_materialized_dot_exact
    (coefficients table : Slice RawQM31)
    (hlen : coefficients.val.length = table.val.length)
    (hbound : coefficients.val.length ≤ 1024)
    (hcoefficients : RuntimeCanonicalList coefficients.val)
    (htable : RuntimeCanonicalList table.val) :
    ∃ out,
      v5_mask.relation_prover.V5IncrementalRelation.materialized_dot
          coefficients table = ok out ∧
      runtimeCanonicalQM31 out ∧
      runtimeQM31View out =
        ∑ row : Fin coefficients.val.length,
          runtimeQM31View coefficients.val[row] * runtimeQM31View table.val[row] := by
  obtain ⟨out, run, canonical, exact⟩ :=
    extracted_materialized_dot_loop_exact coefficients table hlen hbound
      hcoefficients htable aspis_core.field.QM31.ZERO raw_zero_canonical 0#usize (by simp)
  refine ⟨out, run, canonical, ?_⟩
  have exact' := exact
  norm_num at exact'
  rw [exact', raw_zero_exact]
  simp only [zero_add, Nat.Ico_zero_eq_range]
  let summand := fun row : Nat =>
    exactSliceEntry coefficients row * exactSliceEntry table row
  calc
    ∑ row ∈ Finset.range coefficients.val.length, summand row =
        ∑ row : Fin coefficients.val.length, summand row.val :=
      (Fin.sum_univ_eq_sum_range summand coefficients.val.length).symm
    _ = ∑ row : Fin coefficients.val.length,
          runtimeQM31View coefficients.val[row] * runtimeQM31View table.val[row] := by
      apply Finset.sum_congr rfl
      intro row _
      have rb : row.val < coefficients.val.length := row.isLt
      have tb : row.val < table.val.length := by omega
      dsimp only [summand]
      rw [exactSliceEntry_eq coefficients row.val rb,
        exactSliceEntry_eq table row.val tb]
      rfl

/-! ## Exact materialized relation polynomial -/

def RuntimeCanonicalArray {N : Std.Usize} (values : Array RawQM31 N) : Prop :=
  ∀ index, index < N.val → runtimeCanonicalQM31 values.val[index]!

def exactArrayEntry {N : Std.Usize}
    (values : Array RawQM31 N) (index : Nat) : ExactQM31 :=
  runtimeQM31View values.val[index]!

private theorem array_index_run
    {T : Type} [Inhabited T] {N : Std.Usize} (values : Array T N)
    (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have actualBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have hElem : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    simp [actualBound]
  simpa [valueEq, hElem] using run

private theorem array_update_run
    {T : Type} {N : Std.Usize} (values : Array T N)
    (index : Std.Usize) (value : T) (hindex : index.val < N.val) :
    Array.update values index value = ok (values.set index value) := by
  obtain ⟨updated, run, updatedEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec values index value (by
      simpa [Array.length_eq] using hindex))
  simpa [updatedEq] using run

private theorem array_set_get_same
    {N : Std.Usize} (values : Array RawQM31 N)
    (index : Std.Usize) (value : RawQM31) (hindex : index.val < N.val) :
    (values.set index value).val[index.val]! = value := by
  simp only [Array.set_val_eq]
  apply List.set_getElem!_eq
  have h : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  exact ⟨h, rfl⟩

private theorem array_set_get_ne
    {N : Std.Usize} (values : Array RawQM31 N)
    (index : Std.Usize) (value : RawQM31) (other : Nat)
    (hne : other ≠ index.val) :
    (values.set index value).val[other]! = values.val[other]! := by
  simp only [Array.set_val_eq]
  apply List.set_getElem!_ne
  omega

def innerTerm (coefficients : Slice RawQM31)
    (base aDegree : Nat) (dual : Array RawQM31 4#usize)
    (bDegree : Nat) : ExactQM31 :=
  exactSliceEntry coefficients (base + aDegree) *
    exactArrayEntry dual bDegree / 4

def BLoopInvariant
    (coefficients : Slice RawQM31) (base aDegree : Nat)
    (dual : Array RawQM31 4#usize)
    (initial current : Array RawQM31 7#usize) (processed : Nat) : Prop :=
  RuntimeCanonicalArray current ∧
  ∀ degree, degree < 7 →
    exactArrayEntry current degree = exactArrayEntry initial degree +
      ∑ bDegree ∈ Finset.range processed,
        if degree = aDegree + bDegree then
          innerTerm coefficients base aDegree dual bDegree
        else 0

private theorem bLoopInvariant_step
    (coefficients : Slice RawQM31) (base aDegree : Nat)
    (dual : Array RawQM31 4#usize)
    (initial current : Array RawQM31 7#usize)
    (processed : Nat) (hprocessed : processed < 4)
    (updateIndex : Std.Usize)
    (hupdateIndex : updateIndex.val = aDegree + processed)
    (hdegree : aDegree < 4)
    (nextValue : RawQM31)
    (hnextCanonical : runtimeCanonicalQM31 nextValue)
    (hnextExact : runtimeQM31View nextValue =
      exactArrayEntry current (aDegree + processed) +
        innerTerm coefficients base aDegree dual processed)
    (hinvariant : BLoopInvariant coefficients base aDegree dual
      initial current processed) :
    BLoopInvariant coefficients base aDegree dual initial
      (current.set updateIndex nextValue) (processed + 1) := by
  have htarget : aDegree + processed < 7 := by omega
  constructor
  · intro degree hdegreeBound
    by_cases hsame : degree = updateIndex.val
    · subst degree
      rw [array_set_get_same current updateIndex nextValue (by omega)]
      exact hnextCanonical
    · rw [array_set_get_ne current updateIndex nextValue degree hsame]
      exact hinvariant.1 degree hdegreeBound
  · intro degree hdegreeBound
    by_cases hsame : degree = aDegree + processed
    · have hsameIndex : degree = updateIndex.val := by omega
      have hset :
          exactArrayEntry (current.set updateIndex nextValue)
              (aDegree + processed) = runtimeQM31View nextValue := by
        unfold exactArrayEntry
        rw [← hupdateIndex,
          array_set_get_same current updateIndex nextValue (by norm_num; omega)]
      rw [hsame, hset]
      rw [hnextExact, hinvariant.2 (aDegree + processed) htarget,
        Finset.sum_range_succ]
      simp [innerTerm]
    · have hneIndex : degree ≠ updateIndex.val := by omega
      have hset : exactArrayEntry (current.set updateIndex nextValue) degree =
          exactArrayEntry current degree := by
        unfold exactArrayEntry
        rw [array_set_get_ne current updateIndex nextValue degree hneIndex]
      rw [hset, hinvariant.2 degree hdegreeBound, Finset.sum_range_succ]
      simp [hsame]

/-- The innermost generated `b_degree` loop adds the four dual-weighted
products at exactly degrees `a_degree + b_degree`, in ascending Rust order. -/
theorem extracted_materialized_polynomial_b_loop_exact
    (coefficients : Slice RawQM31)
    (output : Array RawQM31 7#usize) (base : Std.Usize)
    (dual : Array RawQM31 4#usize) (aDegree : Std.Usize)
    (hcoeffBound : base.val + aDegree.val < coefficients.val.length)
    (hcoeffLength : coefficients.val.length ≤ 1024)
    (hcoeffCanonical : RuntimeCanonicalList coefficients.val)
    (hdualCanonical : RuntimeCanonicalArray dual)
    (haDegree : aDegree.val < 4)
    (houtputCanonical : RuntimeCanonicalArray output) :
    v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial_loop0_loop0_loop0
        coefficients output base dual aDegree 0#usize
      ⦃ out => BLoopInvariant coefficients base.val aDegree.val dual
        output out 4 ⦄ := by
  simp only [
    v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial_loop0_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : Array RawQM31 7#usize × Std.Usize => 4 - state.2.val)
    (fun state => state.2.val ≤ 4 ∧
      BLoopInvariant coefficients base.val aDegree.val dual
        output state.1 state.2.val)
    (fun out => BLoopInvariant coefficients base.val aDegree.val dual output out 4)
  · rintro ⟨current, bDegree⟩ ⟨hbDegree, hinvariant⟩
    dsimp only at hbDegree hinvariant ⊢
    unfold
      v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial_loop0_loop0_loop0.body
    by_cases hactive : bDegree.val < 4
    · have hactiveScalar : bDegree < 4#usize := by norm_num; omega
      rw [if_pos hactiveScalar]
      simp only [Std.lift, bind_tc_ok]
      have hsmallSize : 1025 < UScalar.size .Usize := by
        simpa using UScalar.hSize (1025#usize)
      have hupdateValue :
          (Std.Usize.wrapping_add aDegree bDegree).val =
            aDegree.val + bDegree.val := by
        apply wrapping_add_exact
        omega
      have hupdateBound :
          (Std.Usize.wrapping_add aDegree bDegree).val < 7 := by omega
      rw [array_index_run current
        (Std.Usize.wrapping_add aDegree bDegree) (by
          simpa using hupdateBound)]
      simp only [bind_tc_ok]
      have hbaseValue :
          (Std.Usize.wrapping_add base aDegree).val =
            base.val + aDegree.val := by
        apply wrapping_add_exact
        omega
      have hbaseBound :
          (Std.Usize.wrapping_add base aDegree).val < coefficients.val.length := by
        omega
      rw [slice_index_run coefficients
        (Std.Usize.wrapping_add base aDegree) hbaseBound]
      simp only [bind_tc_ok]
      rw [array_index_run dual bDegree (by norm_num; omega)]
      simp only [bind_tc_ok]
      have coefficientCanonical := hcoeffCanonical
        coefficients.val[(Std.Usize.wrapping_add base aDegree).val]
          (List.getElem_mem hbaseBound)
      have coefficientBang :
          coefficients.val[(Std.Usize.wrapping_add base aDegree).val]! =
            coefficients.val[(Std.Usize.wrapping_add base aDegree).val] := by
        apply List.getElem!_of_getElem?
        simp [hbaseBound]
      have dualCanonical := hdualCanonical bDegree.val (by norm_num; omega)
      obtain ⟨product, productRun, productCanonical, productExact⟩ :=
        runtime_qm31_mul_corresponds
          coefficients.val[(Std.Usize.wrapping_add base aDegree).val]
          dual.val[bDegree.val]! coefficientCanonical dualCanonical
      rw [productRun]
      simp only [bind_tc_ok]
      obtain ⟨scaled, scaledRun, scaledCanonical, scaledExact⟩ :=
        runtime_qm31_mul_m31_corresponds product
          aspis_core.field.M31_QUARTER productCanonical raw_quarter_canonical
      rw [scaledRun]
      simp only [bind_tc_ok]
      have currentCanonical := hinvariant.1
        (aDegree.val + bDegree.val) (by norm_num; omega)
      obtain ⟨nextValue, addRun, nextCanonical, nextExact⟩ :=
        runtime_qm31_add_corresponds
          current.val[(Std.Usize.wrapping_add aDegree bDegree).val]!
          scaled (by simpa [hupdateValue] using currentCanonical) scaledCanonical
      rw [addRun]
      simp only [bind_tc_ok]
      rw [array_update_run current
        (Std.Usize.wrapping_add aDegree bDegree) nextValue (by
          simpa using hupdateBound)]
      simp only [bind_tc_ok, Std.lift]
      have hnextValue :
          (Std.Usize.wrapping_add bDegree 1#usize).val = bDegree.val + 1 :=
        wrapping_succ_exact bDegree (by omega)
      have currentEntryEq :
          runtimeQM31View
              current.val[(Std.Usize.wrapping_add aDegree bDegree).val]! =
            exactArrayEntry current (aDegree.val + bDegree.val) := by
        unfold exactArrayEntry
        rw [hupdateValue]
      have coefficientEntryEq :
          runtimeQM31View
              coefficients.val[(Std.Usize.wrapping_add base aDegree).val] =
            exactSliceEntry coefficients (base.val + aDegree.val) := by
        calc
          runtimeQM31View
              coefficients.val[(Std.Usize.wrapping_add base aDegree).val] =
              runtimeQM31View
                coefficients.val[(Std.Usize.wrapping_add base aDegree).val]! :=
            congrArg runtimeQM31View coefficientBang.symm
          _ = exactSliceEntry coefficients (base.val + aDegree.val) := by
            unfold exactSliceEntry
            rw [hbaseValue]
      have hnextExact' : runtimeQM31View nextValue =
          exactArrayEntry current (aDegree.val + bDegree.val) +
            innerTerm coefficients base.val aDegree.val dual bDegree.val := by
        rw [nextExact, currentEntryEq, scaledExact, productExact,
          coefficientEntryEq, raw_quarter_exact]
        simp only [innerTerm, exactArrayEntry, exactSliceEntry, div_eq_mul_inv]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hnextValue]
        omega
      · rw [hnextValue]
        apply bLoopInvariant_step coefficients base.val aDegree.val dual
          output current bDegree.val hactive
          (Std.Usize.wrapping_add aDegree bDegree) hupdateValue haDegree
          nextValue nextCanonical hnextExact' hinvariant
      · rw [hnextValue]
        omega
    · have hdone : bDegree.val = 4 := by omega
      have hdoneScalar : ¬ bDegree < 4#usize := by norm_num; omega
      rw [if_neg hdoneScalar]
      simpa [hdone] using hinvariant
  · refine ⟨by norm_num, houtputCanonical, ?_⟩
    intro degree hdegree
    simp

def ALoopInvariant
    (coefficients : Slice RawQM31) (base : Nat)
    (dual : Array RawQM31 4#usize)
    (initial current : Array RawQM31 7#usize) (processed : Nat) : Prop :=
  RuntimeCanonicalArray current ∧
  ∀ degree, degree < 7 →
    exactArrayEntry current degree = exactArrayEntry initial degree +
      ∑ aDegree ∈ Finset.range processed,
        ∑ bDegree ∈ Finset.range 4,
          if degree = aDegree + bDegree then
            innerTerm coefficients base aDegree dual bDegree
          else 0

private theorem aLoopInvariant_step
    (coefficients : Slice RawQM31) (base : Nat)
    (dual : Array RawQM31 4#usize)
    (initial current next : Array RawQM31 7#usize)
    (processed : Nat)
    (houter : ALoopInvariant coefficients base dual initial current processed)
    (hinner : BLoopInvariant coefficients base processed dual current next 4) :
    ALoopInvariant coefficients base dual initial next (processed + 1) := by
  constructor
  · exact hinner.1
  · intro degree hdegree
    rw [hinner.2 degree hdegree, houter.2 degree hdegree]
    have outerSucc := Finset.sum_range_succ
      (fun aDegree =>
        ∑ bDegree ∈ Finset.range 4,
          if degree = aDegree + bDegree then
            innerTerm coefficients base aDegree dual bDegree
          else 0)
      processed
    rw [outerSucc]
    ring

/-- The generated `a_degree` loop composes the four exact inner loops into one
complete degree-three by degree-three convolution chunk. -/
theorem extracted_materialized_polynomial_a_loop_exact
    (coefficients : Slice RawQM31)
    (output : Array RawQM31 7#usize) (base : Std.Usize)
    (dual : Array RawQM31 4#usize)
    (hchunkBound : base.val + 4 ≤ coefficients.val.length)
    (hcoeffLength : coefficients.val.length ≤ 1024)
    (hcoeffCanonical : RuntimeCanonicalList coefficients.val)
    (hdualCanonical : RuntimeCanonicalArray dual)
    (houtputCanonical : RuntimeCanonicalArray output) :
    v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial_loop0_loop0
        coefficients output base dual 0#usize
      ⦃ out => ALoopInvariant coefficients base.val dual output out 4 ⦄ := by
  simp only [
    v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : Array RawQM31 7#usize × Std.Usize => 4 - state.2.val)
    (fun state => state.2.val ≤ 4 ∧
      ALoopInvariant coefficients base.val dual output state.1 state.2.val)
    (fun out => ALoopInvariant coefficients base.val dual output out 4)
  · rintro ⟨current, aDegree⟩ ⟨haDegree, hinvariant⟩
    dsimp only at haDegree hinvariant ⊢
    unfold
      v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial_loop0_loop0.body
    by_cases hactive : aDegree.val < 4
    · have hactiveScalar : aDegree < 4#usize := by norm_num; omega
      rw [if_pos hactiveScalar]
      have hinnerSpec :=
        extracted_materialized_polynomial_b_loop_exact coefficients current base dual
          aDegree (by omega) hcoeffLength hcoeffCanonical hdualCanonical hactive
          hinvariant.1
      obtain ⟨next, hinnerRun, hinner⟩ := Aeneas.Std.WP.spec_imp_exists hinnerSpec
      rw [hinnerRun]
      simp only [bind_tc_ok, Std.lift]
      have hnextValue :
          (Std.Usize.wrapping_add aDegree 1#usize).val = aDegree.val + 1 :=
        wrapping_succ_exact aDegree (by omega)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hnextValue]
        omega
      · rw [hnextValue]
        exact aLoopInvariant_step coefficients base.val dual output current next
          aDegree.val hinvariant hinner
      · rw [hnextValue]
        omega
    · have hdone : aDegree.val = 4 := by omega
      have hdoneScalar : ¬ aDegree < 4#usize := by norm_num; omega
      rw [if_neg hdoneScalar]
      simpa [hdone] using hinvariant
  · refine ⟨by norm_num, houtputCanonical, ?_⟩
    intro degree hdegree
    simp

def dualOffset (degree : Nat) : Nat :=
  match degree with
  | 0 => 0
  | 1 => 3
  | 2 => 2
  | _ => 1

def fibreTerm (coefficients table : Slice RawQM31)
    (fibre aDegree bDegree : Nat) : ExactQM31 :=
  exactSliceEntry coefficients (4 * fibre + aDegree) *
    exactSliceEntry table (4 * fibre + dualOffset bDegree) / 4

def fibreChunk (coefficients table : Slice RawQM31)
    (fibre degree : Nat) : ExactQM31 :=
  ∑ aDegree ∈ Finset.range 4,
    ∑ bDegree ∈ Finset.range 4,
      if degree = aDegree + bDegree then
        fibreTerm coefficients table fibre aDegree bDegree
      else 0

def FibrePrefixInvariant
    (coefficients table : Slice RawQM31)
    (initial current : Array RawQM31 7#usize) (processed : Nat) : Prop :=
  RuntimeCanonicalArray current ∧
  ∀ degree, degree < 7 →
    exactArrayEntry current degree = exactArrayEntry initial degree +
      ∑ fibre ∈ Finset.range processed,
        fibreChunk coefficients table fibre degree

private theorem fibrePrefixInvariant_step
    (coefficients table : Slice RawQM31)
    (initial current next : Array RawQM31 7#usize)
    (processed : Nat) (base : Std.Usize)
    (dual : Array RawQM31 4#usize)
    (hbase : base.val = 4 * processed)
    (hdual : ∀ bDegree, bDegree < 4 →
      exactArrayEntry dual bDegree =
        exactSliceEntry table (4 * processed + dualOffset bDegree))
    (hprefix : FibrePrefixInvariant coefficients table initial current processed)
    (hchunk : ALoopInvariant coefficients base.val dual current next 4) :
    FibrePrefixInvariant coefficients table initial next (processed + 1) := by
  constructor
  · exact hchunk.1
  · intro degree hdegree
    rw [hchunk.2 degree hdegree, hprefix.2 degree hdegree]
    have termEq : ∀ aDegree ∈ Finset.range 4,
        ∀ bDegree ∈ Finset.range 4,
          innerTerm coefficients base.val aDegree dual bDegree =
            fibreTerm coefficients table processed aDegree bDegree := by
      intro aDegree ha bDegree hb
      have ha' := Finset.mem_range.mp ha
      have hb' := Finset.mem_range.mp hb
      unfold innerTerm fibreTerm
      rw [hbase, hdual bDegree hb']
    have chunkEq :
        (∑ aDegree ∈ Finset.range 4,
          ∑ bDegree ∈ Finset.range 4,
            if degree = aDegree + bDegree then
              innerTerm coefficients base.val aDegree dual bDegree
            else 0) = fibreChunk coefficients table processed degree := by
      unfold fibreChunk
      apply Finset.sum_congr rfl
      intro aDegree ha
      apply Finset.sum_congr rfl
      intro bDegree hb
      by_cases hsame : degree = aDegree + bDegree
      · rw [if_pos hsame, if_pos hsame, termEq aDegree ha bDegree hb]
      · rw [if_neg hsame, if_neg hsame]
    rw [chunkEq]
    have prefixSucc := Finset.sum_range_succ
      (fun fibre => fibreChunk coefficients table fibre degree) processed
    rw [prefixSucc]
    ring

/-- The outer generated fibre loop consumes every consecutive four-row chunk
and composes its exact convolution into the seven released coefficients. -/
theorem extracted_materialized_polynomial_outer_loop_exact
    (n : Nat) (coefficients table : Slice RawQM31)
    (output : Array RawQM31 7#usize)
    (hcoeffLength : coefficients.val.length = 4 * n)
    (htableLength : table.val.length = 4 * n)
    (hbound : 4 * n ≤ 1024)
    (hcoeffCanonical : RuntimeCanonicalList coefficients.val)
    (htableCanonical : RuntimeCanonicalList table.val)
    (houtputCanonical : RuntimeCanonicalArray output) :
    v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial_loop0
        coefficients table output 0#usize
      ⦃ out => FibrePrefixInvariant coefficients table output out n ⦄ := by
  simp only [
    v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial_loop0]
  apply loop.spec_decr_nat
    (fun state : Array RawQM31 7#usize × Std.Usize => 4 * n - state.2.val)
    (fun state => ∃ processed,
      state.2.val = 4 * processed ∧ processed ≤ n ∧
        FibrePrefixInvariant coefficients table output state.1 processed)
    (fun out => FibrePrefixInvariant coefficients table output out n)
  · rintro ⟨current, base⟩ ⟨processed, hbase, hprocessed, hprefix⟩
    dsimp only at hbase hprocessed hprefix ⊢
    unfold
      v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial_loop0.body
    by_cases hactive : processed < n
    · have hactiveScalar : base < coefficients.len := by
        simpa [Slice.len_val, hcoeffLength, hbase] using
          (show 4 * processed < 4 * n by omega)
      rw [if_pos hactiveScalar]
      have hbaseBound : base.val < table.val.length := by omega
      rw [slice_index_run table base hbaseBound]
      simp only [bind_tc_ok, Std.lift]
      have hsmallSize : 1025 < UScalar.size .Usize := by
        simpa using UScalar.hSize (1025#usize)
      have hplus3 : (Std.Usize.wrapping_add base 3#usize).val = base.val + 3 := by
        apply wrapping_add_exact
        have hsum : base.val + 3 < UScalar.size .Usize := by omega
        simpa using hsum
      have hplus3Bound :
          (Std.Usize.wrapping_add base 3#usize).val < table.val.length := by
        omega
      rw [slice_index_run table (Std.Usize.wrapping_add base 3#usize)
        hplus3Bound]
      simp only [bind_tc_ok]
      have hplus2 : (Std.Usize.wrapping_add base 2#usize).val = base.val + 2 := by
        apply wrapping_add_exact
        have hsum : base.val + 2 < UScalar.size .Usize := by omega
        simpa using hsum
      have hplus2Bound :
          (Std.Usize.wrapping_add base 2#usize).val < table.val.length := by
        omega
      rw [slice_index_run table (Std.Usize.wrapping_add base 2#usize)
        hplus2Bound]
      simp only [bind_tc_ok]
      have hplus1 : (Std.Usize.wrapping_add base 1#usize).val = base.val + 1 := by
        apply wrapping_add_exact
        have hsum : base.val + 1 < UScalar.size .Usize := by omega
        simpa using hsum
      have hplus1Bound :
          (Std.Usize.wrapping_add base 1#usize).val < table.val.length := by
        omega
      rw [slice_index_run table (Std.Usize.wrapping_add base 1#usize)
        hplus1Bound]
      simp only [bind_tc_ok]
      let dual : Array RawQM31 4#usize := Array.make 4#usize [
        table.val[base.val],
        table.val[(Std.Usize.wrapping_add base 3#usize).val],
        table.val[(Std.Usize.wrapping_add base 2#usize).val],
        table.val[(Std.Usize.wrapping_add base 1#usize).val]]
      have hdualGet0 : dual.val[0]! = table.val[base.val] := by rfl
      have hdualGet1 : dual.val[1]! =
          table.val[(Std.Usize.wrapping_add base 3#usize).val] := by rfl
      have hdualGet2 : dual.val[2]! =
          table.val[(Std.Usize.wrapping_add base 2#usize).val] := by rfl
      have hdualGet3 : dual.val[3]! =
          table.val[(Std.Usize.wrapping_add base 1#usize).val] := by rfl
      have hcanon0 : runtimeCanonicalQM31 table.val[base.val] :=
        htableCanonical table.val[base.val] (List.getElem_mem hbaseBound)
      have hcanon3 : runtimeCanonicalQM31
          table.val[(Std.Usize.wrapping_add base 3#usize).val] :=
        htableCanonical _ (List.getElem_mem hplus3Bound)
      have hcanon2 : runtimeCanonicalQM31
          table.val[(Std.Usize.wrapping_add base 2#usize).val] :=
        htableCanonical _ (List.getElem_mem hplus2Bound)
      have hcanon1 : runtimeCanonicalQM31
          table.val[(Std.Usize.wrapping_add base 1#usize).val] :=
        htableCanonical _ (List.getElem_mem hplus1Bound)
      have hdualCanonical : RuntimeCanonicalArray dual := by
        intro degree hdegree
        have hdegree' : degree < 4 := by simpa using hdegree
        interval_cases degree
        · rw [hdualGet0]
          exact hcanon0
        · rw [hdualGet1]
          exact hcanon3
        · rw [hdualGet2]
          exact hcanon2
        · rw [hdualGet3]
          exact hcanon1
      have hexact0 : runtimeQM31View table.val[base.val] =
          exactSliceEntry table (4 * processed) := by
        calc
          runtimeQM31View table.val[base.val] =
              runtimeQM31View table.val[4 * processed] := by
                simpa only [hbase]
          _ = exactSliceEntry table (4 * processed) :=
            (exactSliceEntry_eq table (4 * processed) (by omega)).symm
      have hexact3 :
          runtimeQM31View
              table.val[(Std.Usize.wrapping_add base 3#usize).val] =
            exactSliceEntry table (4 * processed + 3) := by
        calc
          runtimeQM31View
              table.val[(Std.Usize.wrapping_add base 3#usize).val] =
              runtimeQM31View table.val[4 * processed + 3] := by
                simpa only [hplus3, hbase]
          _ = exactSliceEntry table (4 * processed + 3) :=
            (exactSliceEntry_eq table (4 * processed + 3) (by omega)).symm
      have hexact2 :
          runtimeQM31View
              table.val[(Std.Usize.wrapping_add base 2#usize).val] =
            exactSliceEntry table (4 * processed + 2) := by
        calc
          runtimeQM31View
              table.val[(Std.Usize.wrapping_add base 2#usize).val] =
              runtimeQM31View table.val[4 * processed + 2] := by
                simpa only [hplus2, hbase]
          _ = exactSliceEntry table (4 * processed + 2) :=
            (exactSliceEntry_eq table (4 * processed + 2) (by omega)).symm
      have hexact1 :
          runtimeQM31View
              table.val[(Std.Usize.wrapping_add base 1#usize).val] =
            exactSliceEntry table (4 * processed + 1) := by
        calc
          runtimeQM31View
              table.val[(Std.Usize.wrapping_add base 1#usize).val] =
              runtimeQM31View table.val[4 * processed + 1] := by
                simpa only [hplus1, hbase]
          _ = exactSliceEntry table (4 * processed + 1) :=
            (exactSliceEntry_eq table (4 * processed + 1) (by omega)).symm
      have hdual : ∀ bDegree, bDegree < 4 →
          exactArrayEntry dual bDegree =
            exactSliceEntry table (4 * processed + dualOffset bDegree) := by
        intro bDegree hbDegree
        interval_cases bDegree
        · unfold exactArrayEntry
          rw [hdualGet0]
          simpa [dualOffset] using hexact0
        · unfold exactArrayEntry
          rw [hdualGet1]
          simpa [dualOffset] using hexact3
        · unfold exactArrayEntry
          rw [hdualGet2]
          simpa [dualOffset] using hexact2
        · unfold exactArrayEntry
          rw [hdualGet3]
          simpa [dualOffset] using hexact1
      have hcoeffBound1024 : coefficients.val.length ≤ 1024 := by omega
      have hchunkSpec := extracted_materialized_polynomial_a_loop_exact
        coefficients current base dual (by omega) hcoeffBound1024 hcoeffCanonical
          hdualCanonical hprefix.1
      obtain ⟨next, hchunkRun, hchunk⟩ :=
        Aeneas.Std.WP.spec_imp_exists hchunkSpec
      change
        v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial_loop0_loop0
            coefficients current base dual 0#usize = ok next at hchunkRun
      rw [hchunkRun]
      simp only [bind_tc_ok, Std.lift]
      have hnextBase :
          (Std.Usize.wrapping_add base 4#usize).val = base.val + 4 := by
        apply wrapping_add_exact
        have hsum : base.val + 4 < UScalar.size .Usize := by omega
        simpa using hsum
      refine ⟨⟨processed + 1, ?_, ?_, ?_⟩, ?_⟩
      · rw [hnextBase, hbase]
        ring
      · omega
      · exact fibrePrefixInvariant_step coefficients table output current next
          processed base dual hbase hdual hprefix hchunk
      · rw [hnextBase, hbase]
        omega
    · have hdone : processed = n := by omega
      have hdoneScalar : ¬ base < coefficients.len := by
        simp [Slice.len_val, hcoeffLength, hbase, hdone]
      rw [if_neg hdoneScalar]
      simpa [hdone] using hprefix
  · refine ⟨0, by norm_num, by omega, houtputCanonical, ?_⟩
    intro degree hdegree
    simp

/-- The source-extracted public materialized-polynomial helper returns exactly
the sum of its consecutive four-row convolution chunks.  In particular, the
generated zero-initialized seven-coordinate accumulator contributes no hidden
constant term. -/
theorem extracted_materialized_polynomial_exact
    (n : Nat) (coefficients table : Slice RawQM31)
    (hcoeffLength : coefficients.val.length = 4 * n)
    (htableLength : table.val.length = 4 * n)
    (hbound : 4 * n ≤ 1024)
    (hcoeffCanonical : RuntimeCanonicalList coefficients.val)
    (htableCanonical : RuntimeCanonicalList table.val) :
    ∃ out,
      v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial
          coefficients table = ok out ∧
      RuntimeCanonicalArray out ∧
      ∀ degree, degree < 7 →
        exactArrayEntry out degree =
          ∑ fibre ∈ Finset.range n,
            fibreChunk coefficients table fibre degree := by
  let initial : Array RawQM31 7#usize :=
    Array.repeat 7#usize aspis_core.field.QM31.ZERO
  have hinitialCanonical : RuntimeCanonicalArray initial := by
    intro degree hdegree
    have hdegree' : degree < 7 := by simpa using hdegree
    change runtimeCanonicalQM31
      (Array.repeat 7#usize aspis_core.field.QM31.ZERO).val[degree]!
    have hrepeat :
      (Array.repeat 7#usize aspis_core.field.QM31.ZERO).val[degree]! =
        aspis_core.field.QM31.ZERO := by
      interval_cases degree <;> rfl
    rw [hrepeat]
    exact raw_zero_canonical
  have hinitialExact : ∀ degree, degree < 7 →
      exactArrayEntry initial degree = 0 := by
    intro degree hdegree
    unfold exactArrayEntry
    change runtimeQM31View
      (Array.repeat 7#usize aspis_core.field.QM31.ZERO).val[degree]! = 0
    have hrepeat :
      (Array.repeat 7#usize aspis_core.field.QM31.ZERO).val[degree]! =
        aspis_core.field.QM31.ZERO := by
      interval_cases degree <;> rfl
    rw [hrepeat]
    exact raw_zero_exact
  have hspec := extracted_materialized_polynomial_outer_loop_exact
    n coefficients table initial hcoeffLength htableLength hbound
      hcoeffCanonical htableCanonical hinitialCanonical
  obtain ⟨out, hrun, hinvariant⟩ := Aeneas.Std.WP.spec_imp_exists hspec
  refine ⟨out, ?_, hinvariant.1, ?_⟩
  · simpa [v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial,
      initial] using hrun
  · intro degree hdegree
    rw [hinvariant.2 degree hdegree, hinitialExact degree hdegree, zero_add]

/-! ## Identification with the maintained relation-row map -/

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCRelationRowLinearity

/-- One exact generated four-row chunk is the maintained
`accumulateChunkLinear` map, including the deployed `[w0,w3,w2,w1]/4` order. -/
theorem fibreChunk_eq_accumulateChunkLinear
    (n : Nat) (coefficients table : Slice RawQM31)
    (fibre : Fin n) (degree : Fin 7) :
    fibreChunk coefficients table fibre.val degree.val =
      accumulateChunkLinear
        (fun slot => exactSliceEntry table (childIndex fibre slot).val)
        (fun slot => exactSliceEntry coefficients (childIndex fibre slot).val)
        degree := by
  rw [accumulateChunkLinear_apply]
  fin_cases degree <;>
    simp [fibreChunk, fibreTerm, dualOffset, childIndex,
      Finset.sum_range_succ] <;> ring

/-- Runtime slices, interpreted in the exact maintained field and indexed by
their mathematical fixed length. -/
def exactSliceVector (n : Nat) (values : Slice RawQM31) : Fin n → ExactQM31 :=
  fun index => exactSliceEntry values index.val

/-- The generated materialized OOD helper is the maintained `dotLinear` map
for the very table it returns. -/
theorem extracted_materialized_dot_eq_dotLinear
    (coefficients table : Slice RawQM31)
    (hlen : coefficients.val.length = table.val.length)
    (hbound : coefficients.val.length ≤ 1024)
    (hcoeffCanonical : RuntimeCanonicalList coefficients.val)
    (htableCanonical : RuntimeCanonicalList table.val) :
    ∃ out,
      v5_mask.relation_prover.V5IncrementalRelation.materialized_dot
          coefficients table = ok out ∧
      runtimeCanonicalQM31 out ∧
      runtimeQM31View out =
        dotLinear (exactSliceVector coefficients.val.length table)
          (exactSliceVector coefficients.val.length coefficients) := by
  obtain ⟨out, hrun, hcanonical, hexact⟩ :=
    extracted_materialized_dot_exact coefficients table hlen hbound
      hcoeffCanonical htableCanonical
  refine ⟨out, hrun, hcanonical, ?_⟩
  rw [hexact, dotLinear_apply]
  apply Finset.sum_congr rfl
  intro row _
  have hcoeff : row.val < coefficients.val.length := row.isLt
  have htable : row.val < table.val.length := by omega
  unfold exactSliceVector
  rw [exactSliceEntry_eq coefficients row.val hcoeff,
    exactSliceEntry_eq table row.val htable]
  congr

/-- Summing every generated four-row chunk is literally the maintained
`polynomialForExtension` map, not merely an extensionally similar polynomial. -/
theorem fibreChunk_sum_eq_polynomialForExtension
    (n : Nat) (coefficients table : Slice RawQM31) (degree : Fin 7) :
    (∑ fibre ∈ Finset.range n,
        fibreChunk coefficients table fibre degree.val) =
      polynomialForExtension n (exactSliceVector (4 * n) table)
          (exactSliceVector (4 * n) coefficients) degree := by
  rw [polynomialForExtension_apply]
  simp only [Finset.sum_apply]
  calc
    (∑ fibre ∈ Finset.range n,
        fibreChunk coefficients table fibre degree.val) =
        ∑ fibre : Fin n,
          fibreChunk coefficients table fibre.val degree.val :=
      (Fin.sum_univ_eq_sum_range
        (fun fibre => fibreChunk coefficients table fibre degree.val) n).symm
    _ = ∑ fibre : Fin n,
          accumulateChunkLinear
            (fun slot => exactSliceEntry table (childIndex fibre slot).val)
            (fun slot => exactSliceEntry coefficients
              (childIndex fibre slot).val) degree := by
      apply Finset.sum_congr rfl
      intro fibre _
      exact fibreChunk_eq_accumulateChunkLinear n coefficients table fibre degree
    _ = ∑ fibre : Fin n,
          accumulateChunkLinear
            (fun slot => exactSliceVector (4 * n) table (childIndex fibre slot))
            (fun slot => exactSliceVector (4 * n) coefficients
              (childIndex fibre slot)) degree := by
      rfl

/-- Capstone for the generated public arithmetic helper: its seven returned
coordinates are exactly the maintained `polynomialForExtension` output for the
same returned weight table and coefficient slice. -/
theorem extracted_materialized_polynomial_eq_polynomialForExtension
    (n : Nat) (coefficients table : Slice RawQM31)
    (hcoeffLength : coefficients.val.length = 4 * n)
    (htableLength : table.val.length = 4 * n)
    (hbound : 4 * n ≤ 1024)
    (hcoeffCanonical : RuntimeCanonicalList coefficients.val)
    (htableCanonical : RuntimeCanonicalList table.val) :
    ∃ out,
      v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial
          coefficients table = ok out ∧
      RuntimeCanonicalArray out ∧
      ∀ degree : Fin 7,
        exactArrayEntry out degree.val =
          polynomialForExtension n (exactSliceVector (4 * n) table)
            (exactSliceVector (4 * n) coefficients) degree := by
  obtain ⟨out, hrun, hcanonical, hexact⟩ :=
    extracted_materialized_polynomial_exact n coefficients table hcoeffLength
      htableLength hbound hcoeffCanonical htableCanonical
  refine ⟨out, hrun, hcanonical, ?_⟩
  intro degree
  rw [hexact degree.val degree.isLt,
    fibreChunk_sum_eq_polynomialForExtension n coefficients table degree]

/-- A successful execution of the actual public `polynomial_with_table` method
forces its returned polynomial to be the output of the generated materialized
helper on the returned table.  This is an inversion theorem over the authentic
Rust control flow, including both order checks and the boundary check. -/
theorem polynomial_with_table_success_has_materialized_calls
    (self next : v5_mask.relation_prover.V5IncrementalRelation)
    (polynomial : Array RawQM31 7#usize)
    (table : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table self =
        ok (core.result.Result.Ok (polynomial, table), next)) :
    v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
        self.weights (alloc.vec.Vec.len self.coefficients) = ok table ∧
      v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial
          (alloc.vec.Vec.deref self.coefficients)
          (alloc.vec.Vec.deref table) = ok polynomial := by
  unfold v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table at hrun
  split at hrun
  · simp at hrun
  split at hrun
  · simp at hrun
  dsimp only at hrun
  generalize hweights :
      v5_mask.relation_prover.V5IncrementalRelation.materialize_weights
        self.weights (alloc.vec.Vec.len self.coefficients) = weightsResult at hrun
  cases weightsResult with
  | fail error => simp only [bind_tc_fail] at hrun; cases hrun
  | div => simp only [bind_tc_div] at hrun; cases hrun
  | ok weights =>
    simp only [bind_tc_ok] at hrun
    generalize hpoly :
      v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial
        (alloc.vec.Vec.deref self.coefficients) (alloc.vec.Vec.deref weights) =
          polynomialResult at hrun
    cases polynomialResult with
    | fail error => simp only [bind_tc_fail] at hrun; cases hrun
    | div => simp only [bind_tc_div] at hrun; cases hrun
    | ok actualPolynomial =>
      simp only [bind_tc_ok] at hrun
      generalize hboundary : aspis_core.sumcheck.boundary_sum actualPolynomial =
        boundaryResult at hrun
      cases boundaryResult with
      | fail error => simp at hrun
      | div => simp at hrun
      | ok boundary =>
        simp only [bind_tc_ok] at hrun
        generalize hne :
          core.cmp.PartialEq.ne.trait_default
            aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 boundary
              self.running_claim = neResult at hrun
        cases neResult with
        | fail error => simp at hrun
        | div => simp at hrun
        | ok differs =>
          simp only [bind_tc_ok] at hrun
          split at hrun
          · simp at hrun
          generalize hupdate : Array.update self.sumchecks self.round
            actualPolynomial = updateResult at hrun
          cases updateResult with
          | fail error => simp at hrun
          | div => simp at hrun
          | ok updated =>
            simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq,
              core.result.Result.Ok.injEq] at hrun
            rcases hrun with ⟨⟨hpolyOut, htableOut⟩, _⟩
            subst polynomial
            subst table
            exact ⟨rfl, hpoly⟩

theorem polynomial_with_table_success_has_materialized_call
    (self next : v5_mask.relation_prover.V5IncrementalRelation)
    (polynomial : Array RawQM31 7#usize)
    (table : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table self =
        ok (core.result.Result.Ok (polynomial, table), next)) :
    v5_mask.relation_prover.V5IncrementalRelation.materialized_polynomial
        (alloc.vec.Vec.deref self.coefficients)
        (alloc.vec.Vec.deref table) = ok polynomial :=
  (polynomial_with_table_success_has_materialized_calls
    self next polynomial table hrun).2

/-- The actual public Rust method, on every successful execution and canonical
accepted slice, returns the maintained relation polynomial for its returned
weight table. -/
theorem polynomial_with_table_success_eq_polynomialForExtension
    (n : Nat)
    (self next : v5_mask.relation_prover.V5IncrementalRelation)
    (polynomial : Array RawQM31 7#usize)
    (table : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.relation_prover.V5IncrementalRelation.polynomial_with_table self =
        ok (core.result.Result.Ok (polynomial, table), next))
    (hcoeffLength : self.coefficients.val.length = 4 * n)
    (htableLength : table.val.length = 4 * n)
    (hbound : 4 * n ≤ 1024)
    (hcoeffCanonical : RuntimeCanonicalList self.coefficients.val)
    (htableCanonical : RuntimeCanonicalList table.val) :
    RuntimeCanonicalArray polynomial ∧
    ∀ degree : Fin 7,
      exactArrayEntry polynomial degree.val =
        polynomialForExtension n
          (exactSliceVector (4 * n) (alloc.vec.Vec.deref table))
          (exactSliceVector (4 * n) (alloc.vec.Vec.deref self.coefficients))
          degree := by
  have hcall := polynomial_with_table_success_has_materialized_call
    self next polynomial table hrun
  obtain ⟨out, hout, hcanonical, hexact⟩ :=
    extracted_materialized_polynomial_eq_polynomialForExtension n
      (alloc.vec.Vec.deref self.coefficients) (alloc.vec.Vec.deref table)
      hcoeffLength htableLength hbound hcoeffCanonical htableCanonical
  have heq : out = polynomial := by
    rw [hout] at hcall
    exact Result.ok.inj hcall
  subst out
  exact ⟨hcanonical, hexact⟩

#print axioms extracted_materialized_dot_loop_exact
#print axioms extracted_materialized_dot_exact
#print axioms extracted_materialized_polynomial_outer_loop_exact
#print axioms extracted_materialized_polynomial_exact
#print axioms fibreChunk_eq_accumulateChunkLinear
#print axioms fibreChunk_sum_eq_polynomialForExtension
#print axioms extracted_materialized_polynomial_eq_polynomialForExtension
#print axioms extracted_materialized_dot_eq_dotLinear
#print axioms polynomial_with_table_success_has_materialized_call
#print axioms polynomial_with_table_success_eq_polynomialForExtension

end aspis_prover.ComponentCRuntimeMaterializedRelationArithmetic
