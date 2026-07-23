import RuntimePackerMaintainedOutput

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimePackerSixSegmentBridge

open aspis_prover
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCConcreteDownstream
open AspisV5ComponentCDownstreamDeployed
open AspisV5ComponentCRelationRowLinearity
open ComponentCRuntimePackerProof
open ComponentCRuntimePackerMaintainedOutput

abbrev RawQM31 := aspis_core.field.QM31

@[simp] private theorem array3_val_zero {T : Type} [Inhabited T]
    (a b c : T) : (Array.make 3#usize [a, b, c]).val[0]! = a := by
  simp [Array.make]

@[simp] private theorem array3_val_one {T : Type} [Inhabited T]
    (a b c : T) : (Array.make 3#usize [a, b, c]).val[1]! = b := by
  simp [Array.make]

@[simp] private theorem array3_val_two {T : Type} [Inhabited T]
    (a b c : T) : (Array.make 3#usize [a, b, c]).val[2]! = c := by
  simp [Array.make]

private theorem finSum_inl_val {m n : Nat} (x : Fin m) :
    (finSumFinEquiv (n := n) (Sum.inl x)).val = x.val := rfl

private theorem finSum_inr_val {m n : Nat} (x : Fin n) :
    (finSumFinEquiv (m := m) (Sum.inr x)).val = m + x.val := rfl

private theorem finProd_val {m n : Nat} (x : Fin m × Fin n) :
    (finProdFinEquiv x).val = x.2.val + n * x.1.val := rfl

private theorem ftag_relation_ood_val
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (rt : DeployedRuntimeSchedule F K) (round : Fin 4) (sample : Fin 2) :
    (fTaggedIndexEquiv (decodeFriSchedule rt)
      (.inl (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample)))).val =
        9 * round.val + sample.val := by
  change sample.val + 9 * round.val = _
  omega

private theorem ftag_relation_polynomial_val
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (rt : DeployedRuntimeSchedule F K) (round : Fin 4) (degree : Fin 7) :
    (fTaggedIndexEquiv (decodeFriSchedule rt)
      (.inl (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree)))).val =
        9 * round.val + 2 + degree.val := by
  change (2 + degree.val) + 9 * round.val = _
  omega

private theorem laterIndex_one_val
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (rt : DeployedRuntimeSchedule F K)
    (index : Fin rt.later1Count) (slot : Fin 4) :
    (laterIndexEquiv (decodeFriSchedule rt) (.inl (index, slot))).val =
      slot.val + 4 * index.val := by
  unfold laterIndexEquiv laterRows
  rw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    finSum_inl_val, finProd_val]

private theorem laterIndex_two_val
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (rt : DeployedRuntimeSchedule F K)
    (index : Fin rt.later2Count) (slot : Fin 4) :
    (laterIndexEquiv (decodeFriSchedule rt) (.inr (.inl (index, slot)))).val =
      4 * rt.later1Count + (slot.val + 4 * index.val) := by
  unfold laterIndexEquiv laterRows
  rw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    finSum_inr_val, finSum_inl_val, finProd_val]
  simp only [decodeFriSchedule_later1Count, decodeFriSchedule_later2Count]
  omega

private theorem laterIndex_three_val
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (rt : DeployedRuntimeSchedule F K)
    (index : Fin rt.later3Count) (slot : Fin 4) :
    (laterIndexEquiv (decodeFriSchedule rt) (.inr (.inr (index, slot)))).val =
      4 * rt.later1Count + 4 * rt.later2Count +
        (slot.val + 4 * index.val) := by
  unfold laterIndexEquiv laterRows
  rw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    finSum_inr_val, finSum_inr_val, finProd_val]
  simp only [decodeFriSchedule_later1Count, decodeFriSchedule_later2Count,
    decodeFriSchedule_later3Count]
  omega

private theorem ftag_later1_val
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (rt : DeployedRuntimeSchedule F K)
    (index : Fin rt.later1Count) (slot : Fin 4) :
    (fTaggedIndexEquiv (decodeFriSchedule rt)
      (.inr (.inl (.inl (index, slot))))).val =
        36 + 4 * index.val + slot.val := by
  change relationRowsCount +
    (laterIndexEquiv (decodeFriSchedule rt) (.inl (index, slot))).val = _
  rw [laterIndex_one_val]
  norm_num [relationRowsCount]
  omega

private theorem ftag_later2_val
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (rt : DeployedRuntimeSchedule F K)
    (index : Fin rt.later2Count) (slot : Fin 4) :
    (fTaggedIndexEquiv (decodeFriSchedule rt)
      (.inr (.inl (.inr (.inl (index, slot)))))).val =
        36 + 4 * rt.later1Count + 4 * index.val + slot.val := by
  change relationRowsCount +
    (laterIndexEquiv (decodeFriSchedule rt) (.inr (.inl (index, slot)))).val = _
  rw [laterIndex_two_val]
  norm_num [relationRowsCount]
  omega

private theorem ftag_later3_val
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (rt : DeployedRuntimeSchedule F K)
    (index : Fin rt.later3Count) (slot : Fin 4) :
    (fTaggedIndexEquiv (decodeFriSchedule rt)
      (.inr (.inl (.inr (.inr (index, slot)))))).val =
        36 + 4 * rt.later1Count + 4 * rt.later2Count +
          4 * index.val + slot.val := by
  change relationRowsCount +
    (laterIndexEquiv (decodeFriSchedule rt) (.inr (.inr (index, slot)))).val = _
  rw [laterIndex_three_val]
  norm_num [relationRowsCount]
  omega

private theorem ftag_final_val
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (rt : DeployedRuntimeSchedule F K) (coefficient : Fin 4) :
    (fTaggedIndexEquiv (decodeFriSchedule rt)
      (.inr (.inr coefficient))).val =
        36 + 4 * rt.later1Count + 4 * rt.later2Count +
          4 * rt.later3Count + coefficient.val := by
  unfold fTaggedIndexEquiv fRows laterRows
  rw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    finSum_inr_val, finSum_inr_val]
  simp only [relationRowsCount, finalCoefficientCount,
    decodeFriSchedule_later1Count, decodeFriSchedule_later2Count,
    decodeFriSchedule_later3Count]
  change 36 + (rt.later1Count * 4 +
      (rt.later2Count * 4 + rt.later3Count * 4) + coefficient.val) = _
  omega

/-- The literal six-segment raw value sequence consumed by the generated
packer: relation OOD/polynomial rows, three flattened later blocks, then four
final coefficients. -/
def sixSegmentValueAt
    (oodValues : Array (Array RawQM31 2#usize) 4#usize)
    (polynomials : Array (Array RawQM31 7#usize) 4#usize)
    (later0 later1 later2 : alloc.vec.Vec RawQM31)
    (finalCoefficients : Array RawQM31 4#usize) (row : Nat) : RawQM31 :=
  if _ : row < 36 then
    if _ : row % 9 < 2 then
      oodValues.val[row / 9]!.val[row % 9]!
    else
      polynomials.val[row / 9]!.val[row % 9 - 2]!
  else
    let tail0 := row - 36
    if _ : tail0 < later0.val.length then later0.val[tail0]!
    else
      let tail1 := tail0 - later0.val.length
      if _ : tail1 < later1.val.length then later1.val[tail1]!
      else
        let tail2 := tail1 - later1.val.length
        if _ : tail2 < later2.val.length then later2.val[tail2]!
        else finalCoefficients.val[tail2 - later2.val.length]!

private theorem usize_wrapping_sub_exact
    (left right : Std.Usize) (hle : right.val ≤ left.val) :
    (Std.Usize.wrapping_sub left right).val = left.val - right.val := by
  rw [Std.Usize.wrapping_sub_val_eq]
  have hSize : UScalar.size .Usize = Std.Usize.max + 1 := by
    simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
  have hLeftLt : left.val < UScalar.size .Usize := by
    rw [hSize]
    scalar_tac
  have hRightLeSize : right.val ≤ UScalar.size .Usize := by omega
  have hRewrite :
      left.val + (UScalar.size .Usize - right.val) =
        (left.val - right.val) + UScalar.size .Usize := by
    omega
  rw [hRewrite, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

/-- The already-extracted row decoder and value dispatcher agree with the
literal six-segment sequence for every in-range runtime row. -/
theorem generated_value_dispatcher_matches_six_segments
    (oodValues : Array (Array RawQM31 2#usize) 4#usize)
    (polynomials : Array (Array RawQM31 7#usize) 4#usize)
    (later0 later1 later2 : alloc.vec.Vec RawQM31)
    (finalCoefficients : Array RawQM31 4#usize)
    (row : Std.Usize)
    (hrow : row.val <
      40 + later0.val.length + later1.val.length + later2.val.length) :
    v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
        oodValues polynomials
        (Array.make 3#usize [later0, later1, later2])
        finalCoefficients row =
      ok (some (sixSegmentValueAt oodValues polynomials later0 later1 later2
        finalCoefficients row.val)) := by
  let later := Array.make 3#usize [later0, later1, later2]
  have hlaterGet0 : later.val[0]! = later0 := by
    simpa [later] using array3_val_zero later0 later1 later2
  have hlaterGet1 : later.val[1]! = later1 := by
    simpa [later] using array3_val_one later0 later1 later2
  have hlaterGet2 : later.val[2]! = later2 := by
    simpa [later] using array3_val_two later0 later1 later2
  have hlaterGet0U8 : later.val[(0#u8).val]! = later0 := by
    simpa using hlaterGet0
  have hlaterGet1U8 : later.val[(1#u8).val]! = later1 := by
    simpa using hlaterGet1
  have hlaterGet2U8 : later.val[(2#u8).val]! = later2 := by
    simpa using hlaterGet2
  by_cases hrelation : row.val < 36
  · obtain ⟨round, slot, htag, hround, hslot⟩ :=
      generated_relation_row_exact
        (Array.make 3#usize [alloc.vec.Vec.len later0,
          alloc.vec.Vec.len later1, alloc.vec.Vec.len later2]) row hrelation
    have hroundBound : round.val < 4 := by
      rw [hround]
      omega
    by_cases hood : row.val % 9 < 2
    · have hslotBound : slot.val < 2 := by simpa [hslot] using hood
      have hvalue := generated_relation_ood_value_exact oodValues polynomials
        later finalCoefficients row round slot htag hroundBound hslotBound
      simpa [later, sixSegmentValueAt, hrelation, hood, hround, hslot]
        using hvalue
    · have hslotLow : 2 ≤ slot.val := by rw [hslot]; omega
      have hslotHigh : slot.val < 9 := by
        rw [hslot]
        exact Nat.mod_lt _ (by norm_num)
      have hvalue := generated_relation_polynomial_value_exact
        oodValues polynomials later finalCoefficients row round slot htag
        hroundBound hslotLow hslotHigh
      simpa [later, sixSegmentValueAt, hrelation, hood, hround, hslot]
        using hvalue
  · have hrow36 : 36 ≤ row.val := by omega
    let tail0 := Std.Usize.wrapping_sub row 36#usize
    have htail0 : tail0.val = row.val - 36 := by
      exact usize_wrapping_sub_exact row 36#usize (by norm_num at hrow36 ⊢; omega)
    by_cases hlater0 : tail0.val < later0.val.length
    · obtain ⟨index, htag, hindex⟩ := generated_later_zero_row_exact
        (alloc.vec.Vec.len later0) (alloc.vec.Vec.len later1)
        (alloc.vec.Vec.len later2) row tail0 (by rw [htail0]; omega)
        (by simpa using hlater0)
      have hvalue := generated_later_value_exact oodValues polynomials later
        finalCoefficients row 0#u8 index htag (by norm_num) (by
          rw [hlaterGet0U8]
          simpa [hindex] using hlater0)
      have hlater0Nat : row.val - 36 < later0.val.length := by
        rwa [← htail0]
      rw [hlaterGet0U8] at hvalue
      simp [hindex, hlater0] at hvalue
      simpa [later, sixSegmentValueAt, hrelation, hlater0Nat, hindex, htail0]
        using hvalue
    · let tail1 := Std.Usize.wrapping_sub tail0 (alloc.vec.Vec.len later0)
      have htail0Lower : later0.val.length ≤ tail0.val := by omega
      have htail1 : tail1.val = tail0.val - later0.val.length := by
        exact usize_wrapping_sub_exact tail0 (alloc.vec.Vec.len later0)
          (by simpa using htail0Lower)
      by_cases hlater1 : tail1.val < later1.val.length
      · obtain ⟨index, htag, hindex⟩ := generated_later_one_row_exact
          (alloc.vec.Vec.len later0) (alloc.vec.Vec.len later1)
          (alloc.vec.Vec.len later2) row tail1
          (by
            change row.val = 36 + later0.val.length + tail1.val
            rw [htail1, htail0]
            omega)
          (by simpa using hlater1)
        have hvalue := generated_later_value_exact oodValues polynomials later
          finalCoefficients row 1#u8 index htag (by norm_num) (by
            rw [hlaterGet1U8]
            simpa [hindex] using hlater1)
        have hnotLater0Nat : ¬ row.val - 36 < later0.val.length := by
          rwa [← htail0]
        have htail1Nat :
            tail1.val = row.val - 36 - later0.val.length := by
          rw [htail1, htail0]
        have hlater1Nat :
            row.val - 36 - later0.val.length < later1.val.length := by
          rw [← htail1Nat]
          exact hlater1
        rw [hlaterGet1U8] at hvalue
        simp [hindex, hlater1] at hvalue
        simpa [later, sixSegmentValueAt, hrelation, hnotLater0Nat,
          hlater1Nat, hindex, htail1Nat] using hvalue
      · let tail2 := Std.Usize.wrapping_sub tail1 (alloc.vec.Vec.len later1)
        have htail1Lower : later1.val.length ≤ tail1.val := by omega
        have htail2 : tail2.val = tail1.val - later1.val.length := by
          exact usize_wrapping_sub_exact tail1 (alloc.vec.Vec.len later1)
            (by simpa using htail1Lower)
        by_cases hlater2 : tail2.val < later2.val.length
        · obtain ⟨index, htag, hindex⟩ := generated_later_two_row_exact
            (alloc.vec.Vec.len later0) (alloc.vec.Vec.len later1)
            (alloc.vec.Vec.len later2) row tail2
            (by
              change row.val = 36 + later0.val.length + later1.val.length +
                tail2.val
              rw [htail2, htail1, htail0]
              omega)
            (by simpa using hlater2)
          have hvalue := generated_later_value_exact oodValues polynomials later
            finalCoefficients row 2#u8 index htag (by norm_num) (by
              rw [hlaterGet2U8]
              simpa [hindex] using hlater2)
          have hnotLater0Nat : ¬ row.val - 36 < later0.val.length := by
            rwa [← htail0]
          have htail1Nat :
              tail1.val = row.val - 36 - later0.val.length := by
            rw [htail1, htail0]
          have hnotLater1Nat :
              ¬ row.val - 36 - later0.val.length < later1.val.length := by
            rw [← htail1Nat]
            exact hlater1
          have htail2Nat : tail2.val =
              row.val - 36 - later0.val.length - later1.val.length := by
            rw [htail2, htail1Nat]
          have hlater2Nat :
              row.val - 36 - later0.val.length - later1.val.length <
                later2.val.length := by
            rw [← htail2Nat]
            exact hlater2
          rw [hlaterGet2U8] at hvalue
          simp [hindex, hlater2] at hvalue
          simpa [later, sixSegmentValueAt, hrelation, hnotLater0Nat,
            hnotLater1Nat, hlater2Nat, hindex, htail1Nat, htail2Nat]
            using hvalue
        · let tail3 := Std.Usize.wrapping_sub tail2 (alloc.vec.Vec.len later2)
          have htail2Lower : later2.val.length ≤ tail2.val := by omega
          have htail3 : tail3.val = tail2.val - later2.val.length := by
            exact usize_wrapping_sub_exact tail2 (alloc.vec.Vec.len later2)
              (by simpa using htail2Lower)
          have htail3Bound : tail3.val < 4 := by
            rw [htail3, htail2, htail1, htail0]
            omega
          obtain ⟨coefficient, htag, hcoefficient⟩ := generated_final_row_exact
            (alloc.vec.Vec.len later0) (alloc.vec.Vec.len later1)
            (alloc.vec.Vec.len later2) row tail3
            (by
              change row.val = 36 + later0.val.length + later1.val.length +
                later2.val.length + tail3.val
              rw [htail3, htail2, htail1, htail0]
              omega)
            htail3Bound
          have hvalue := generated_final_value_exact oodValues polynomials later
            finalCoefficients row coefficient htag (by
              rw [hcoefficient]
              exact htail3Bound)
          have hnotLater0Nat : ¬ row.val - 36 < later0.val.length := by
            rwa [← htail0]
          have htail1Nat :
              tail1.val = row.val - 36 - later0.val.length := by
            rw [htail1, htail0]
          have hnotLater1Nat :
              ¬ row.val - 36 - later0.val.length < later1.val.length := by
            rw [← htail1Nat]
            exact hlater1
          have htail2Nat : tail2.val =
              row.val - 36 - later0.val.length - later1.val.length := by
            rw [htail2, htail1Nat]
          have hnotLater2Nat :
              ¬ row.val - 36 - later0.val.length - later1.val.length <
                later2.val.length := by
            rw [← htail2Nat]
            exact hlater2
          have htail3Nat : tail3.val =
              row.val - 36 - later0.val.length - later1.val.length -
                later2.val.length := by
            rw [htail3, htail2Nat]
          have hfinalNat :
              row.val - 36 - later0.val.length - later1.val.length -
                later2.val.length < finalCoefficients.val.length := by
            simpa [← htail3Nat] using htail3Bound
          have hfinalBang :
              finalCoefficients.val[
                row.val - 36 - later0.val.length - later1.val.length -
                  later2.val.length]! =
                finalCoefficients.val[
                  row.val - 36 - later0.val.length - later1.val.length -
                    later2.val.length] :=
            getElem!_pos finalCoefficients.val
              (row.val - 36 - later0.val.length - later1.val.length -
                later2.val.length) hfinalNat
          simp [hcoefficient, htail3Bound] at hvalue
          simpa [later, sixSegmentValueAt, hrelation, hnotLater0Nat,
            hnotLater1Nat, hnotLater2Nat, hcoefficient, htail3, htail2,
            htail1, htail0, htail1Nat, htail2Nat, htail3Nat, hfinalNat,
            hfinalBang] using hvalue

#print axioms generated_value_dispatcher_matches_six_segments

section MaintainedSixSegment

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Six explicit arithmetic families are sufficient to discharge the sole
per-row premise of the public packer capstone.  All traversal, row decoding,
segment ordering and output sizing remain conclusions of the extracted Rust
proofs; the hypotheses below contain only decoded field equalities. -/
theorem six_segment_facts_build_rows_match_deployed
    (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (c : CWord K)
    (view : RawQM31 → K)
    (oodValues : Array (Array RawQM31 2#usize) 4#usize)
    (polynomials : Array (Array RawQM31 7#usize) 4#usize)
    (later0 later1 later2 : alloc.vec.Vec RawQM31)
    (finalCoefficients : Array RawQM31 4#usize)
    (hlen0 : later0.val.length = 4 * rt.later1Count)
    (hlen1 : later1.val.length = 4 * rt.later2Count)
    (hlen2 : later2.val.length = 4 * rt.later3Count)
    (hood : ∀ (round : Fin 4) (sample : Fin 2),
      view (oodValues.val[round.val]!.val[sample.val]!) =
        roundOodRows (decodeRelationSchedule rt) round c sample)
    (hpoly : ∀ (round : Fin 4) (degree : Fin 7),
      view (polynomials.val[round.val]!.val[degree.val]!) =
        roundPolynomialRows (decodeRelationSchedule rt) round c degree)
    (hlater0 : ∀ (index : Fin rt.later1Count) (slot : Fin 4),
      view (later0.val[4 * index.val + slot.val]!) =
        later1ReadMap (decodeFriSchedule rt) enc c (index, slot))
    (hlater1 : ∀ (index : Fin rt.later2Count) (slot : Fin 4),
      view (later1.val[4 * index.val + slot.val]!) =
        later2ReadMap (decodeFriSchedule rt) enc c (index, slot))
    (hlater2 : ∀ (index : Fin rt.later3Count) (slot : Fin 4),
      view (later2.val[4 * index.val + slot.val]!) =
        later3ReadMap (decodeFriSchedule rt) enc c (index, slot))
    (hfinal : ∀ coefficient : Fin 4,
      view (finalCoefficients.val[coefficient.val]!) =
        finalCoefficientMap (decodeFriSchedule rt) c coefficient) :
    GeneratedPackerRowsMatchDeployed rt enc c view oodValues polynomials
      (Array.make 3#usize [later0, later1, later2]) finalCoefficients := by
  refine ⟨sixSegmentValueAt oodValues polynomials later0 later1 later2
    finalCoefficients, ?_, ?_⟩
  · intro row hrow
    apply generated_value_dispatcher_matches_six_segments
    rw [deployed_output_dimension] at hrow
    omega
  · intro row
    let tag := (fTaggedIndexEquiv (decodeFriSchedule rt)).symm row
    have htag : fTaggedIndexEquiv (decodeFriSchedule rt) tag = row :=
      (fTaggedIndexEquiv (decodeFriSchedule rt)).apply_symm_apply row
    rcases tag with relation | rest
    · obtain ⟨round, within⟩ := relation
      by_cases hwithin : within.val < 2
      · let sample : Fin 2 := ⟨within.val, hwithin⟩
        have hwithinEq :
            finSumFinEquiv (m := 2) (n := 7) (.inl sample) = within := by
          apply Fin.ext
          rfl
        have hrowEq :
            fTaggedIndexEquiv (decodeFriSchedule rt)
                (.inl (round,
                  finSumFinEquiv (m := 2) (n := 7) (.inl sample))) = row := by
          simpa [hwithinEq] using htag
        rw [← hrowEq, deployed_row_relation_ood,
          ftag_relation_ood_val]
        have hroundLt : round.val < 4 := round.isLt
        have hsampleLt : sample.val < 2 := sample.isLt
        have hrelation : 9 * round.val + sample.val < 36 := by omega
        have hslot : (9 * round.val + sample.val) % 9 = sample.val := by
          omega
        have hround : (9 * round.val + sample.val) / 9 = round.val := by
          omega
        have hoodSlot : (9 * round.val + sample.val) % 9 < 2 := by
          omega
        have hoodRoundBound : round.val < oodValues.val.length := by
          simpa using hroundLt
        have hoodRoundRead :
            oodValues.val[round.val]! = oodValues.val[round.val] :=
          getElem!_pos oodValues.val round.val hoodRoundBound
        simpa [sixSegmentValueAt, hrelation, hoodSlot, hslot, hround,
          hsampleLt, hoodRoundRead]
          using hood round sample
      · have hwithinLow : 2 ≤ within.val := by omega
        have hwithinHigh : within.val < 9 := by
          simpa [relationRowsPerRound] using within.isLt
        let degree : Fin 7 := ⟨within.val - 2, by omega⟩
        have hwithinEq :
            finSumFinEquiv (m := 2) (n := 7) (.inr degree) = within := by
          apply Fin.ext
          change 2 + (within.val - 2) = within.val
          omega
        have hrowEq :
            fTaggedIndexEquiv (decodeFriSchedule rt)
                (.inl (round,
                  finSumFinEquiv (m := 2) (n := 7) (.inr degree))) = row := by
          simpa [hwithinEq] using htag
        rw [← hrowEq, deployed_row_relation_polynomial,
          ftag_relation_polynomial_val]
        have hroundLt : round.val < 4 := round.isLt
        have hdegreeLt : degree.val < 7 := degree.isLt
        have hrelation : 9 * round.val + 2 + degree.val < 36 := by omega
        have hslot : (9 * round.val + 2 + degree.val) % 9 = 2 + degree.val := by
          omega
        have hround : (9 * round.val + 2 + degree.val) / 9 = round.val := by
          omega
        have hpolySlot : ¬ (9 * round.val + 2 + degree.val) % 9 < 2 := by
          omega
        have hpolySlotDirect : ¬ 2 + degree.val ≤ 1 := by omega
        have hdegree :
            (9 * round.val + 2 + degree.val) % 9 - 2 = degree.val := by
          omega
        have hpolyRoundBound : round.val < polynomials.val.length := by
          simpa using hroundLt
        have hpolyRoundRead :
            polynomials.val[round.val]! = polynomials.val[round.val] :=
          getElem!_pos polynomials.val round.val hpolyRoundBound
        simpa [sixSegmentValueAt, hrelation, hpolySlot, hslot, hround,
          hdegree, hpolySlotDirect, hpolyRoundRead] using hpoly round degree
    · rcases rest with later | final
      · rcases later with first | rest
        · obtain ⟨index, slot⟩ := first
          rw [← htag, deployed_row_later1, ftag_later1_val]
          have hindexLt : index.val < rt.later1Count := by
            simpa using index.isLt
          have hslotLt : slot.val < 4 := slot.isLt
          have hrelation : ¬ 36 + 4 * index.val + slot.val < 36 := by omega
          have htail0 :
              36 + 4 * index.val + slot.val - 36 =
                4 * index.val + slot.val := by omega
          have hread0 :
              36 + 4 * index.val + slot.val - 36 < later0.val.length := by
            rw [htail0, hlen0]
            omega
          have hread0Direct :
              4 * index.val + slot.val < later0.val.length := by
            rw [hlen0]
            omega
          simpa [sixSegmentValueAt, hrelation, htail0, hread0, hread0Direct]
            using hlater0 index slot
        · rcases rest with second | third
          · obtain ⟨index, slot⟩ := second
            rw [← htag, deployed_row_later2, ftag_later2_val]
            have hindexLt : index.val < rt.later2Count := by
              simpa using index.isLt
            have hslotLt : slot.val < 4 := slot.isLt
            have hrelation :
                ¬ 36 + 4 * rt.later1Count + 4 * index.val + slot.val < 36 := by
              omega
            have htail0 :
                36 + 4 * rt.later1Count + 4 * index.val + slot.val - 36 =
                  4 * rt.later1Count + 4 * index.val + slot.val := by omega
            have hskip0 :
                ¬ 36 + 4 * rt.later1Count + 4 * index.val + slot.val - 36 <
                  later0.val.length := by
              rw [htail0, hlen0]
              omega
            have htail1 :
                36 + 4 * rt.later1Count + 4 * index.val + slot.val - 36 -
                    later0.val.length = 4 * index.val + slot.val := by
              rw [htail0, hlen0]
              omega
            have hread1 :
                36 + 4 * rt.later1Count + 4 * index.val + slot.val - 36 -
                    later0.val.length < later1.val.length := by
              rw [htail1, hlen1]
              omega
            have hskip0Direct :
                ¬ 4 * rt.later1Count + 4 * index.val + slot.val <
                  later0.val.length := by
              rw [hlen0]
              omega
            have hread1Direct :
                4 * index.val + slot.val < later1.val.length := by
              rw [hlen1]
              omega
            have hread1Middle :
                4 * rt.later1Count + 4 * index.val + slot.val -
                    later0.val.length < later1.val.length := by
              rw [hlen0, hlen1]
              omega
            have hindex1Middle :
                4 * rt.later1Count + 4 * index.val + slot.val -
                    later0.val.length = 4 * index.val + slot.val := by
              rw [hlen0]
              omega
            simpa [sixSegmentValueAt, hrelation, htail0, hskip0, htail1,
              hread1, hskip0Direct, hread1Direct, hread1Middle,
              hindex1Middle]
              using hlater1 index slot
          · obtain ⟨index, slot⟩ := third
            rw [← htag, deployed_row_later3, ftag_later3_val]
            have hindexLt : index.val < rt.later3Count := by
              simpa using index.isLt
            have hslotLt : slot.val < 4 := slot.isLt
            have hrelation :
                ¬ 36 + 4 * rt.later1Count + 4 * rt.later2Count +
                    4 * index.val + slot.val < 36 := by
              omega
            have htail0 :
                36 + 4 * rt.later1Count + 4 * rt.later2Count +
                    4 * index.val + slot.val - 36 =
                  4 * rt.later1Count + 4 * rt.later2Count +
                    4 * index.val + slot.val := by omega
            have hskip0 :
                ¬ 36 + 4 * rt.later1Count + 4 * rt.later2Count +
                    4 * index.val + slot.val - 36 < later0.val.length := by
              rw [htail0, hlen0]
              omega
            have htail1 :
                36 + 4 * rt.later1Count + 4 * rt.later2Count +
                    4 * index.val + slot.val - 36 - later0.val.length =
                  4 * rt.later2Count + 4 * index.val + slot.val := by
              rw [htail0, hlen0]
              omega
            have hskip1 :
                ¬ 36 + 4 * rt.later1Count + 4 * rt.later2Count +
                    4 * index.val + slot.val - 36 - later0.val.length <
                  later1.val.length := by
              rw [htail1, hlen1]
              omega
            have htail2 :
                36 + 4 * rt.later1Count + 4 * rt.later2Count +
                    4 * index.val + slot.val - 36 - later0.val.length -
                    later1.val.length = 4 * index.val + slot.val := by
              rw [htail1, hlen1]
              omega
            have hread2 :
                36 + 4 * rt.later1Count + 4 * rt.later2Count +
                    4 * index.val + slot.val - 36 - later0.val.length -
                    later1.val.length < later2.val.length := by
              rw [htail2, hlen2]
              omega
            have hskip0Direct :
                ¬ 4 * rt.later1Count + 4 * rt.later2Count +
                    4 * index.val + slot.val < later0.val.length := by
              rw [hlen0]
              omega
            have hskip1Direct :
                ¬ 4 * rt.later2Count + 4 * index.val + slot.val <
                  later1.val.length := by
              rw [hlen1]
              omega
            have hread2Direct :
                4 * index.val + slot.val < later2.val.length := by
              rw [hlen2]
              omega
            have hskip1Middle :
                ¬ 4 * rt.later1Count + 4 * rt.later2Count +
                    4 * index.val + slot.val - later0.val.length <
                  later1.val.length := by
              rw [hlen0, hlen1]
              omega
            have hread2Middle :
                4 * rt.later1Count + 4 * rt.later2Count +
                    4 * index.val + slot.val - later0.val.length -
                    later1.val.length < later2.val.length := by
              rw [hlen0, hlen1, hlen2]
              omega
            have hindex2Middle :
                4 * rt.later1Count + 4 * rt.later2Count +
                    4 * index.val + slot.val - later0.val.length -
                    later1.val.length = 4 * index.val + slot.val := by
              rw [hlen0, hlen1]
              omega
            simpa [sixSegmentValueAt, hrelation, htail0, hskip0, htail1,
              hskip1, htail2, hread2, hskip0Direct, hskip1Direct,
              hread2Direct, hskip1Middle, hread2Middle, hindex2Middle]
              using hlater2 index slot
      · rw [← htag, deployed_row_final, ftag_final_val]
        have hfinalLt : final.val < 4 := final.isLt
        have hrelation :
            ¬ 36 + 4 * rt.later1Count + 4 * rt.later2Count +
                4 * rt.later3Count + final.val < 36 := by
          omega
        have htail0 :
            36 + 4 * rt.later1Count + 4 * rt.later2Count +
                4 * rt.later3Count + final.val - 36 =
              4 * rt.later1Count + 4 * rt.later2Count +
                4 * rt.later3Count + final.val := by omega
        have hskip0 :
            ¬ 36 + 4 * rt.later1Count + 4 * rt.later2Count +
                4 * rt.later3Count + final.val - 36 < later0.val.length := by
          rw [htail0, hlen0]
          omega
        have htail1 :
            36 + 4 * rt.later1Count + 4 * rt.later2Count +
                4 * rt.later3Count + final.val - 36 - later0.val.length =
              4 * rt.later2Count + 4 * rt.later3Count + final.val := by
          rw [htail0, hlen0]
          omega
        have hskip1 :
            ¬ 36 + 4 * rt.later1Count + 4 * rt.later2Count +
                4 * rt.later3Count + final.val - 36 - later0.val.length <
              later1.val.length := by
          rw [htail1, hlen1]
          omega
        have htail2 :
            36 + 4 * rt.later1Count + 4 * rt.later2Count +
                4 * rt.later3Count + final.val - 36 - later0.val.length -
                later1.val.length = 4 * rt.later3Count + final.val := by
          rw [htail1, hlen1]
          omega
        have hskip2 :
            ¬ 36 + 4 * rt.later1Count + 4 * rt.later2Count +
                4 * rt.later3Count + final.val - 36 - later0.val.length -
                later1.val.length < later2.val.length := by
          rw [htail2, hlen2]
          omega
        have hfinalIndex :
            36 + 4 * rt.later1Count + 4 * rt.later2Count +
                4 * rt.later3Count + final.val - 36 - later0.val.length -
                later1.val.length - later2.val.length = final.val := by
          rw [htail2, hlen2]
          omega
        have hskip0Direct :
            ¬ 4 * rt.later1Count + 4 * rt.later2Count +
                4 * rt.later3Count + final.val < later0.val.length := by
          rw [hlen0]
          omega
        have hskip1Direct :
            ¬ 4 * rt.later2Count + 4 * rt.later3Count + final.val <
              later1.val.length := by
          rw [hlen1]
          omega
        have hskip2Direct :
            ¬ 4 * rt.later3Count + final.val < later2.val.length := by
          rw [hlen2]
          omega
        have hskip1Middle :
            ¬ 4 * rt.later1Count + 4 * rt.later2Count +
                4 * rt.later3Count + final.val - later0.val.length <
              later1.val.length := by
          rw [hlen0, hlen1]
          omega
        have hskip2Middle :
            ¬ 4 * rt.later1Count + 4 * rt.later2Count +
                4 * rt.later3Count + final.val - later0.val.length -
                later1.val.length < later2.val.length := by
          rw [hlen0, hlen1, hlen2]
          omega
        have hfinalMiddle :
            4 * rt.later1Count + 4 * rt.later2Count +
                4 * rt.later3Count + final.val - later0.val.length -
                later1.val.length - later2.val.length = final.val := by
          rw [hlen0, hlen1, hlen2]
          omega
        have hfinalBound : final.val < finalCoefficients.val.length := by
          simpa using hfinalLt
        have hfinalBang :
            finalCoefficients.val[final.val]! =
              finalCoefficients.val[final.val] :=
          getElem!_pos finalCoefficients.val final.val hfinalBound
        simpa [sixSegmentValueAt, hrelation, htail0, hskip0, htail1,
          hskip1, htail2, hskip2, hfinalIndex, hskip0Direct, hskip1Direct,
          hskip2Direct, hskip1Middle, hskip2Middle, hfinalMiddle, hfinalBang]
          using hfinal final

#print axioms six_segment_facts_build_rows_match_deployed

end MaintainedSixSegment

end aspis_prover.ComponentCRuntimePackerSixSegmentBridge
