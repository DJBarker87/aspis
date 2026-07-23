import RuntimeSquareInstantiation
import RuntimeMaterializedRelationArithmetic

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow

namespace aspis_prover.ComponentCRuntimeCoefficientFoldCorrespondence

open aspis_prover
open ComponentCRuntimeFoldPrimitiveInstantiation
open ComponentCRuntimeSquareInstantiation

abbrev RawQM31 := aspis_core.field.QM31

local instance : Inhabited RawQM31 := ⟨aspis_core.field.QM31.ZERO⟩

def RuntimeCanonicalList (values : List RawQM31) : Prop :=
  ∀ value ∈ values, runtimeCanonicalQM31 value

def exactSliceEntry (values : Slice RawQM31) (index : Nat) : ExactQM31 :=
  runtimeQM31View values.val[index]!

def coefficientFoldAt
    (values : Slice RawQM31) (alpha : ExactQM31) (fibre : Nat) : ExactQM31 :=
  exactSliceEntry values (4 * fibre) +
    alpha * exactSliceEntry values (4 * fibre + 1) +
    alpha ^ 2 * exactSliceEntry values (4 * fibre + 2) +
    alpha ^ 3 * exactSliceEntry values (4 * fibre + 3)

private theorem slice_index_run
    (values : Slice RawQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    Slice.index_usize values index = ok values.val[index.val] := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq]
  simp [hindex]

private theorem wrapping_add_exact
    (left right : Std.Usize)
    (hsum : left.val + right.val < UScalar.size .Usize) :
    (Std.Usize.wrapping_add left right).val = left.val + right.val := by
  rw [Std.Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt hsum]

private theorem getElem_bang_eq
    (values : List RawQM31) (index : Nat) (hindex : index < values.length) :
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

/-- The exact source-extracted natural arity-four loop, from an arbitrary
already-correct prefix.  This is the order-sensitive vector theorem: it
authenticates every four consecutive reads, every append, and the `+4`
cursor update in the generated Rust loop. -/
theorem extracted_coefficient_fold_loop_exact
    (values : Slice RawQM31) (alpha alphaSquared alphaCubed : RawQM31)
    (n k : Nat)
    (hvaluesLength : values.val.length = 4 * n)
    (hn : n ≤ 256)
    (hk : k ≤ n)
    (hvaluesCanonical : RuntimeCanonicalList values.val)
    (halpha : runtimeCanonicalQM31 alpha)
    (halphaSquared : runtimeCanonicalQM31 alphaSquared)
    (halphaCubed : runtimeCanonicalQM31 alphaCubed)
    (halphaSquaredView :
      runtimeQM31View alphaSquared = runtimeQM31View alpha ^ 2)
    (halphaCubedView :
      runtimeQM31View alphaCubed = runtimeQM31View alpha ^ 3)
    (folded : alloc.vec.Vec RawQM31)
    (hfoldedLength : folded.val.length = k)
    (hfoldedCanonical : RuntimeCanonicalList folded.val)
    (hfoldedExact : ∀ j, j < k →
      runtimeQM31View folded.val[j]! =
        coefficientFoldAt values (runtimeQM31View alpha) j)
    (start : Std.Usize) (hstart : start.val = 4 * k) :
    ∃ out,
      circle_candidate.fold_adjacent_natural_arity4_loop
          values alpha alphaSquared alphaCubed folded start = ok out ∧
      out.val.length = n ∧
      RuntimeCanonicalList out.val ∧
      ∀ j, j < n →
        runtimeQM31View out.val[j]! =
          coefficientFoldAt values (runtimeQM31View alpha) j := by
  by_cases hmore : k < n
  · have hstart4 : start.val + 4 = 4 * (k + 1) := by omega
    have hsmall : start.val + 4 < UScalar.size .Usize := by
      have hsize : 1025 < UScalar.size .Usize := by
        have h := (1025#usize).hSize
        scalar_tac
      omega
    let afterFour := Std.Usize.wrapping_add start circle_candidate.FIBER_SLOTS
    have hafterFour : afterFour.val = start.val + 4 := by
      unfold afterFour circle_candidate.FIBER_SLOTS
      exact wrapping_add_exact start 4#usize hsmall
    have hcondition : afterFour ≤ values.len := by
      rw [UScalar.le_equiv]
      simp only [hafterFour, Slice.len_val, hvaluesLength, hstart]
      omega
    have h0 : start.val < values.val.length := by omega
    let i1 := Std.Usize.wrapping_add start 1#usize
    let i2 := Std.Usize.wrapping_add start 2#usize
    let i3 := Std.Usize.wrapping_add start 3#usize
    have hi1 : i1.val = start.val + 1 := wrapping_add_exact _ _ (by
      simpa [hstart] using (show 4 * k + 1 < UScalar.size .Usize by omega))
    have hi2 : i2.val = start.val + 2 := wrapping_add_exact _ _ (by
      simpa [hstart] using (show 4 * k + 2 < UScalar.size .Usize by omega))
    have hi3 : i3.val = start.val + 3 := wrapping_add_exact _ _ (by
      simpa [hstart] using (show 4 * k + 3 < UScalar.size .Usize by omega))
    have h1 : i1.val < values.val.length := by omega
    have h2 : i2.val < values.val.length := by omega
    have h3 : i3.val < values.val.length := by omega
    have read0 := slice_index_run values start h0
    have read1 := slice_index_run values i1 h1
    have read2 := slice_index_run values i2 h2
    have read3 := slice_index_run values i3 h3
    have can0 := hvaluesCanonical values.val[start.val] (List.getElem_mem h0)
    have can1 := hvaluesCanonical values.val[i1.val] (List.getElem_mem h1)
    have can2 := hvaluesCanonical values.val[i2.val] (List.getElem_mem h2)
    have can3 := hvaluesCanonical values.val[i3.val] (List.getElem_mem h3)
    obtain ⟨t1, ht1, ct1, et1⟩ :=
      runtime_qm31_mul_corresponds alpha values.val[i1.val] halpha can1
    obtain ⟨s1, hs1, cs1, es1⟩ :=
      runtime_qm31_add_corresponds values.val[start.val] t1 can0 ct1
    obtain ⟨t2, ht2, ct2, et2⟩ :=
      runtime_qm31_mul_corresponds alphaSquared values.val[i2.val]
        halphaSquared can2
    obtain ⟨s2, hs2, cs2, es2⟩ :=
      runtime_qm31_add_corresponds s1 t2 cs1 ct2
    obtain ⟨t3, ht3, ct3, et3⟩ :=
      runtime_qm31_mul_corresponds alphaCubed values.val[i3.val]
        halphaCubed can3
    obtain ⟨value, hvalue, cvalue, evalue⟩ :=
      runtime_qm31_add_corresponds s2 t3 cs2 ct3
    have hcapacity : folded.val.length < Std.Usize.max := by
      rw [hfoldedLength]
      have hmax : 1024 < Std.Usize.max := by
        have h := (1025#usize).hSize
        scalar_tac
      omega
    obtain ⟨foldedNext, hpush, hfoldedNext⟩ := Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.push_spec folded value hcapacity)
    let startNext := Std.Usize.wrapping_add start circle_candidate.FIBER_SLOTS
    have hstartNext : startNext.val = 4 * (k + 1) := by
      rw [show startNext.val = start.val + 4 by
        unfold startNext circle_candidate.FIBER_SLOTS
        exact wrapping_add_exact start 4#usize hsmall]
      omega
    have hbody :
        circle_candidate.fold_adjacent_natural_arity4_loop.body
            values alpha alphaSquared alphaCubed folded start =
          ok (cont (foldedNext, startNext)) := by
      unfold circle_candidate.fold_adjacent_natural_arity4_loop.body
      simp only [Std.lift, bind_tc_ok]
      rw [if_pos hcondition, read0]
      simp only [bind_tc_ok]
      change (do
        let q1 ← Slice.index_usize values i1
        let q2 ← aspis_core.field.QM31.mul alpha q1
        let q3 ← aspis_core.field.QM31.add values.val[start.val] q2
        let q4 ← Slice.index_usize values i2
        let q5 ← aspis_core.field.QM31.mul alphaSquared q4
        let q6 ← aspis_core.field.QM31.add q3 q5
        let q7 ← Slice.index_usize values i3
        let q8 ← aspis_core.field.QM31.mul alphaCubed q7
        let q9 ← aspis_core.field.QM31.add q6 q8
        let folded1 ← alloc.vec.Vec.push folded q9
        let start1 ← lift startNext
        ok (cont (folded1, start1))) = ok (cont (foldedNext, startNext))
      rw [read1]
      simp only [bind_tc_ok]
      rw [ht1]
      simp only [bind_tc_ok]
      rw [hs1]
      simp only [bind_tc_ok]
      rw [read2]
      simp only [bind_tc_ok]
      rw [ht2]
      simp only [bind_tc_ok]
      rw [hs2]
      simp only [bind_tc_ok]
      rw [read3]
      simp only [bind_tc_ok]
      rw [ht3]
      simp only [bind_tc_ok]
      rw [hvalue]
      simp only [bind_tc_ok]
      rw [hpush]
      rfl
    have hfoldedNextLength : foldedNext.val.length = k + 1 := by
      rw [hfoldedNext, List.length_append]
      simp [hfoldedLength]
    have hfoldedNextCanonical : RuntimeCanonicalList foldedNext.val := by
      intro x hx
      rw [hfoldedNext] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hfoldedCanonical x hx
      · have hxEq : x = value := List.mem_singleton.mp hx
        subst x
        exact cvalue
    have valueExact :
        runtimeQM31View value =
          coefficientFoldAt values (runtimeQM31View alpha) k := by
      rw [evalue, es2, es1, et1, et2, et3,
        halphaSquaredView, halphaCubedView]
      unfold coefficientFoldAt exactSliceEntry
      have hk0 : 4 * k < values.val.length := by omega
      have hk1 : 4 * k + 1 < values.val.length := by omega
      have hk2 : 4 * k + 2 < values.val.length := by omega
      have hk3 : 4 * k + 3 < values.val.length := by omega
      rw [getElem_bang_eq values.val (4 * k) hk0,
        getElem_bang_eq values.val (4 * k + 1) hk1,
        getElem_bang_eq values.val (4 * k + 2) hk2,
        getElem_bang_eq values.val (4 * k + 3) hk3]
      simp only [hstart, hi1, hi2, hi3]
    have hfoldedNextExact : ∀ j, j < k + 1 →
        runtimeQM31View foldedNext.val[j]! =
          coefficientFoldAt values (runtimeQM31View alpha) j := by
      intro j hj
      rw [hfoldedNext]
      by_cases hjk : j < k
      · rw [appended_prefix_get folded.val value j (by omega)]
        exact hfoldedExact j hjk
      · have hjEq : j = k := by omega
        subst j
        have hlast := appended_last_get folded.val value
        rw [hfoldedLength] at hlast
        rw [hlast]
        exact valueExact
    rw [circle_candidate.fold_adjacent_natural_arity4_loop, loop.eq_1]
    simp only [Prod.fst, Prod.snd]
    rw [hbody]
    simp only [bind_tc_ok]
    obtain ⟨out, hout, houtLength, houtCanonical, houtExact⟩ :=
      extracted_coefficient_fold_loop_exact values alpha alphaSquared alphaCubed
        n (k + 1) hvaluesLength hn (by omega) hvaluesCanonical
        halpha halphaSquared halphaCubed halphaSquaredView halphaCubedView
        foldedNext hfoldedNextLength hfoldedNextCanonical hfoldedNextExact
        startNext hstartNext
    have hout' :
        loop
            (fun state =>
              circle_candidate.fold_adjacent_natural_arity4_loop.body
                values alpha alphaSquared alphaCubed state.1 state.2)
            (foldedNext, startNext) = ok out := by
      simpa only [circle_candidate.fold_adjacent_natural_arity4_loop] using hout
    rw [hout']
    exact ⟨out, rfl, houtLength, houtCanonical, houtExact⟩
  · have hkEq : k = n := by omega
    have hsmall : start.val + 4 < UScalar.size .Usize := by
      have hsize : 1029 < UScalar.size .Usize := by
        have h := (1029#usize).hSize
        scalar_tac
      omega
    let afterFour := Std.Usize.wrapping_add start circle_candidate.FIBER_SLOTS
    have hafterFour : afterFour.val = start.val + 4 := by
      unfold afterFour circle_candidate.FIBER_SLOTS
      exact wrapping_add_exact start 4#usize hsmall
    have hcondition : ¬ afterFour ≤ values.len := by
      intro hle
      have hv : afterFour.val ≤ values.len.val :=
        (UScalar.le_equiv afterFour values.len).mp hle
      simp [hafterFour, Slice.len_val, hvaluesLength, hstart, hkEq] at hv
    have hbody :
        circle_candidate.fold_adjacent_natural_arity4_loop.body
            values alpha alphaSquared alphaCubed folded start = ok (done folded) := by
      unfold circle_candidate.fold_adjacent_natural_arity4_loop.body
      simp only [Std.lift, bind_tc_ok]
      rw [if_neg hcondition]
    rw [circle_candidate.fold_adjacent_natural_arity4_loop, loop.eq_1]
    simp only [Prod.fst, Prod.snd]
    rw [hbody]
    refine ⟨folded, rfl, ?_, hfoldedCanonical, ?_⟩
    · omega
    · intro j hj
      exact hfoldedExact j (by omega)
termination_by n - k
decreasing_by omega

private theorem emptyVecCanonical (capacity : Std.Usize) :
    RuntimeCanonicalList
      (alloc.vec.Vec.with_capacity RawQM31 capacity).val := by
  intro value hvalue
  simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] at hvalue

/-- The actual public Rust entrypoint computes `alpha²`, then `alpha³`, and
runs the source-extracted vector loop from the empty output. -/
theorem extracted_fold_adjacent_natural_arity4_exact
    (values : Slice RawQM31) (alpha : RawQM31) (n : Nat)
    (hvaluesLength : values.val.length = 4 * n)
    (hn : n ≤ 256)
    (hvaluesCanonical : RuntimeCanonicalList values.val)
    (halpha : runtimeCanonicalQM31 alpha) :
    ∃ out,
      circle_candidate.fold_adjacent_natural_arity4 values alpha = ok out ∧
      out.val.length = n ∧
      RuntimeCanonicalList out.val ∧
      ∀ j, j < n →
        runtimeQM31View out.val[j]! =
          coefficientFoldAt values (runtimeQM31View alpha) j := by
  obtain ⟨alphaSquared, hsquare, hcanonicalSquared, hexactSquared⟩ :=
    runtime_qm31_square_corresponds alpha halpha
  obtain ⟨alphaCubed, hcube, hcanonicalCubed, hexactCubed⟩ :=
    runtime_qm31_mul_corresponds alphaSquared alpha hcanonicalSquared halpha
  have hexactCubed' :
      runtimeQM31View alphaCubed = runtimeQM31View alpha ^ 3 := by
    rw [hexactCubed, hexactSquared]
    ring
  obtain ⟨capacity, hcapacity, _hcapacityValue⟩ :=
    UScalar.div_spec values.len
      (y := circle_candidate.FIBER_SLOTS) (by
        simp [circle_candidate.FIBER_SLOTS])
  let empty := alloc.vec.Vec.with_capacity RawQM31 capacity
  have hemptyLength : empty.val.length = 0 := by
    rfl
  have hemptyExact : ∀ j, j < 0 →
      runtimeQM31View empty.val[j]! =
        coefficientFoldAt values (runtimeQM31View alpha) j := by
    intro j hj
    omega
  obtain ⟨out, hloop, houtLength, houtCanonical, houtExact⟩ :=
    extracted_coefficient_fold_loop_exact values alpha alphaSquared alphaCubed
      n 0 hvaluesLength hn (by omega) hvaluesCanonical halpha
      hcanonicalSquared hcanonicalCubed hexactSquared hexactCubed'
      empty hemptyLength (emptyVecCanonical capacity) hemptyExact 0#usize (by rfl)
  refine ⟨out, ?_, houtLength, houtCanonical, houtExact⟩
  unfold circle_candidate.fold_adjacent_natural_arity4
  rw [hsquare]
  simp only [bind_tc_ok]
  rw [hcube]
  simp only [bind_tc_ok]
  rw [hcapacity]
  simpa only [bind_tc_ok, empty] using hloop

private def coefficientInputView
    (values : Slice RawQM31) (n : Nat) : Fin (4 * n) → ExactQM31 :=
  fun row => runtimeQM31View values.val[row.val]!

private theorem coefficientFoldAt_eq_layer
    (values : Slice RawQM31) (alpha : ExactQM31) (n : Nat)
    (hvaluesLength : values.val.length = 4 * n) (fibre : Fin n) :
    coefficientFoldAt values alpha fibre.val =
      AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer n alpha
        (coefficientInputView values n) fibre := by
  have h0 : 4 * fibre.val < values.val.length := by omega
  have h1 : 4 * fibre.val + 1 < values.val.length := by omega
  have h2 : 4 * fibre.val + 2 < values.val.length := by omega
  have h3 : 4 * fibre.val + 3 < values.val.length := by omega
  rw [AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer_apply]
  unfold AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue
    coefficientFoldAt exactSliceEntry coefficientInputView
  rfl

/-- Maintained-model capstone for one complete natural coefficient fold.  The
theorem is universal in all canonical source values and fixes the deployed
fibre-major child order `4*i+s`. -/
theorem generated_coefficient_fold_equals_maintained_layer
    (values : Slice RawQM31) (alpha : RawQM31) (n : Nat)
    (hvaluesLength : values.val.length = 4 * n)
    (hn : n ≤ 256)
    (hvaluesCanonical : RuntimeCanonicalList values.val)
    (halpha : runtimeCanonicalQM31 alpha) :
    ∃ out,
      circle_candidate.fold_adjacent_natural_arity4 values alpha = ok out ∧
      out.val.length = n ∧
      RuntimeCanonicalList out.val ∧
      ∀ fibre : Fin n,
        runtimeQM31View out.val[fibre.val]! =
          AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer n
            (runtimeQM31View alpha) (coefficientInputView values n) fibre := by
  obtain ⟨out, hrun, hlen, hcanonical, hexact⟩ :=
    extracted_fold_adjacent_natural_arity4_exact values alpha n hvaluesLength
      hn hvaluesCanonical halpha
  refine ⟨out, hrun, hlen, hcanonical, ?_⟩
  intro fibre
  rw [hexact fibre.val fibre.isLt]
  exact coefficientFoldAt_eq_layer values (runtimeQM31View alpha) n
    hvaluesLength fibre

#print axioms extracted_coefficient_fold_loop_exact
#print axioms extracted_fold_adjacent_natural_arity4_exact
#print axioms generated_coefficient_fold_equals_maintained_layer

end aspis_prover.ComponentCRuntimeCoefficientFoldCorrespondence
