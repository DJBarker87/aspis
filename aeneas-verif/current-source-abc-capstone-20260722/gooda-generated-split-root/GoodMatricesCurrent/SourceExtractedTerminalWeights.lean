import GoodMatricesCurrent.SourceExtractedTerminalFieldAll

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedTerminalWeights

open GoodMatricesCurrent.SourceExtractedTerminalField

abbrev LocalPoint := Array LocalQM31 10#usize
abbrev LocalWeights := Array LocalQM31 64#usize

def pointEntry (point : LocalPoint) (index : Fin 10) : LocalQM31 :=
  point.val[index.val]'(by rw [point.property]; exact index.isLt)

def pointToExact (point : LocalPoint) : Fin 10 → ExactQM31 :=
  fun index => qm31ToExact (pointEntry point index)

def CanonicalLocalPoint (point : LocalPoint) : Prop :=
  ∀ index : Fin 10, CanonicalLocalQM31 (pointEntry point index)

def weightEntry (weights : LocalWeights) (index : Fin 64) : LocalQM31 :=
  weights.val[index.val]'(by rw [weights.property]; exact index.isLt)

def weightsToExact (weights : LocalWeights) : Fin 64 → ExactQM31 :=
  fun index => qm31ToExact (weightEntry weights index)

def CanonicalLocalWeights (weights : LocalWeights) : Prop :=
  ∀ index : Fin 64, CanonicalLocalQM31 (weightEntry weights index)

@[simp] theorem weightEntry_set_same (weights : LocalWeights)
    (index : Std.Usize) (hindex : index.val < 64) (value : LocalQM31) :
    weightEntry (weights.set index value) ⟨index.val, hindex⟩ = value := by
  unfold weightEntry
  exact List.getElem_set_self (by
    simp only [List.length_set]
    rw [weights.property]
    exact hindex)

@[simp] theorem weightEntry_set_other (weights : LocalWeights)
    (index : Std.Usize) (value : LocalQM31) (output : Fin 64)
    (hne : index.val ≠ output.val) :
    weightEntry (weights.set index value) output = weightEntry weights output := by
  unfold weightEntry
  exact List.getElem_set_ne hne (by
    simp only [List.length_set]
    rw [weights.property]
    exact output.isLt)

theorem canonical_weights_set (weights : LocalWeights)
    (index : Std.Usize) (hindex : index.val < 64) (value : LocalQM31)
    (hweights : CanonicalLocalWeights weights)
    (hvalue : CanonicalLocalQM31 value) :
    CanonicalLocalWeights (weights.set index value) := by
  intro output
  by_cases heq : index.val = output.val
  · have hout : output = ⟨index.val, hindex⟩ := Fin.ext heq.symm
    subst output
    simpa using hvalue
  · rw [weightEntry_set_other weights index value output heq]
    exact hweights output

theorem point_index_call (point : LocalPoint) (index : Std.Usize)
    (hindex : index.val < 10) :
    Array.index_usize point index =
      .ok (pointEntry point ⟨index.val, hindex⟩) := by
  exact Array.index_usize_eq_ok_of_getElem_eq point index
    (by rw [point.property]; exact hindex) _ rfl

theorem weight_index_call (weights : LocalWeights) (index : Std.Usize)
    (hindex : index.val < 64) :
    Array.index_usize weights index =
      .ok (weightEntry weights ⟨index.val, hindex⟩) := by
  exact Array.index_usize_eq_ok_of_getElem_eq weights index
    (by rw [weights.property]; exact hindex) _ rfl

theorem weight_update_call (weights : LocalWeights) (index : Std.Usize)
    (hindex : index.val < 64) (value : LocalQM31) :
    Array.update weights index value = .ok (weights.set index value) := by
  exact Array.update_eq_ok _ _ _ (by rw [weights.property]; exact hindex)

def zeroLocalQM31 : LocalQM31 :=
  { c0 := { a := 0#u32, b := 0#u32 },
    c1 := { a := 0#u32, b := 0#u32 } }

def oneLocalQM31 : LocalQM31 :=
  { c0 := { a := 1#u32, b := 0#u32 },
    c1 := { a := 0#u32, b := 0#u32 } }

def zeroWeights : LocalWeights := Array.repeat 64#usize zeroLocalQM31

def initialWeights : LocalWeights := zeroWeights.set 0#usize oneLocalQM31

theorem zeroWeights_canonical : CanonicalLocalWeights zeroWeights := by
  intro index
  unfold weightEntry zeroWeights
  simpa only [Array.repeat_val, List.getElem_replicate, zeroLocalQM31]
    using local_zero_canonical

theorem zeroWeights_exact (index : Fin 64) :
    weightsToExact zeroWeights index = 0 := by
  unfold weightsToExact weightEntry zeroWeights
  simpa only [Array.repeat_val, List.getElem_replicate, zeroLocalQM31]
    using local_zero_exact

theorem initialWeights_canonical : CanonicalLocalWeights initialWeights := by
  have honeCanonical : CanonicalLocalQM31 oneLocalQM31 := by
    simpa [oneLocalQM31] using local_one_canonical
  exact canonical_weights_set zeroWeights 0#usize (by simp) oneLocalQM31
    zeroWeights_canonical honeCanonical

theorem initialWeights_exact_zero : weightsToExact initialWeights 0 = 1 := by
  unfold weightsToExact initialWeights
  have hfin : (0 : Fin 64) =
      ⟨(0#usize : Std.Usize).val, by simp⟩ := by
    apply Fin.ext
    rfl
  rw [hfin, weightEntry_set_same]
  simpa [oneLocalQM31] using local_one_exact

def suffixRec (point : Fin 10 → ExactQM31) : Nat → Nat → ExactQM31
  | 0, index => if index = 0 then 1 else 0
  | count + 1, index =>
      if hcount : count < 7 then
        suffixRec point count (index / 2) *
          (if index % 2 = 0 then 1 - point ⟨3 + count, by omega⟩
            else point ⟨3 + count, by omega⟩)
      else 0

def exactSuffixWeight (point : Fin 10 → ExactQM31) (index : Fin 64) :
    ExactQM31 := suffixRec point 6 index.val

theorem suffixRec_succ (point : Fin 10 → ExactQM31)
    (count index : Nat) (hcount : count < 7) :
    suffixRec point (count + 1) index =
      suffixRec point count (index / 2) *
        (if index % 2 = 0 then 1 - point ⟨3 + count, by omega⟩
          else point ⟨3 + count, by omega⟩) := by
  rw [suffixRec, dif_pos hcount]

theorem suffixRec_zero_active (index : Nat) (hindex : index < 1) :
    suffixRec point 0 index = 1 := by
  have : index = 0 := by omega
  subst index
  rfl

theorem initialWeights_active (index : Fin 64) (hindex : index.val < 1) :
    weightsToExact initialWeights index = suffixRec point 0 index.val := by
  have hzero : index = 0 := Fin.ext (by omega)
  subst index
  rw [initialWeights_exact_zero]
  rfl

theorem usize_wrapping_sub_one_val (index : Std.Usize)
    (hpositive : 1 ≤ index.val) :
    (Std.Usize.wrapping_sub index 1#usize).val = index.val - 1 := by
  rw [Std.Usize.wrapping_sub_val_eq]
  have hone : (1#usize : Std.Usize).val = 1 := by rfl
  rw [hone]
  have hindex := index.hSize
  have hrearrange :
      index.val + (UScalar.size .Usize - 1) =
        (index.val - 1) + UScalar.size .Usize := by omega
  rw [hrearrange, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem usize_wrapping_mul_two_val (index : Std.Usize)
    (hbound : 2 * index.val < Std.Usize.size) :
    (Std.Usize.wrapping_mul 2#usize index).val = 2 * index.val := by
  rw [Std.Usize.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [Nat.mul_comm] using hbound

theorem usize_wrapping_add_one_val (index : Std.Usize)
    (hbound : index.val + 1 < Std.Usize.size) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa using hbound

def ExpandedEntry (base : Fin 64 → ExactQM31) (coordinate : ExactQM31)
    (index : Fin 64) : ExactQM31 :=
  base ⟨index.val / 2, by omega⟩ *
    (if index.val % 2 = 0 then 1 - coordinate else coordinate)

def InnerInvariant (base : Fin 64 → ExactQM31) (coordinate : ExactQM31)
    (weights : LocalWeights) (index width : Std.Usize) : Prop :=
  CanonicalLocalWeights weights ∧
  index.val ≤ width.val ∧ width.val ≤ 32 ∧
  (∀ output : Fin 64, output.val < index.val →
    weightsToExact weights output = base output) ∧
  (∀ output : Fin 64, 2 * index.val ≤ output.val →
    output.val < 2 * width.val →
    weightsToExact weights output = ExpandedEntry base coordinate output)

private abbrev innerBody :=
  v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights_loop0_loop0.body

private abbrev innerLoop :=
  v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights_loop0_loop0

private theorem pred_lt_of_eq_sub_one {current next : Nat}
    (hpositive : 1 ≤ current) (hnext : next = current - 1) :
    next < current := by
  omega

private theorem eq_zero_of_not_one_le {value : Nat}
    (h : ¬ 1 ≤ value) : value = 0 := by
  omega

theorem innerBody_step (base : Fin 64 → ExactQM31)
    (coordinate : ExactQM31) (localCoordinate : LocalQM31)
    (prepared : _root_.aspis_core.field.PreparedQm31Multiplier)
    (weights : LocalWeights) (index width : Std.Usize)
    (hcoordinateCanonical : CanonicalLocalQM31 localCoordinate)
    (hcoordinateExact : qm31ToExact localCoordinate = coordinate)
    (hprepared : PreparedFor prepared localCoordinate)
    (hpositive : 1 ≤ index.val)
    (hinvariant : InnerInvariant base coordinate weights index width) :
    ∃ state : LocalWeights × Std.Usize,
      innerBody prepared weights index = .ok (.cont state) ∧
      state.2.val = index.val - 1 ∧
      InnerInvariant base coordinate state.1 state.2 width := by
  rcases hinvariant with
    ⟨hweightsCanonical, hindexWidth, hwidth, hunprocessed, hprocessed⟩
  let parentIndex := Std.Usize.wrapping_sub index 1#usize
  have hparentIndex : parentIndex.val = index.val - 1 :=
    usize_wrapping_sub_one_val index hpositive
  have hparentBound : parentIndex.val < 64 := by omega
  have hparentCall := weight_index_call weights parentIndex hparentBound
  let parent := weightEntry weights ⟨parentIndex.val, hparentBound⟩
  have hparentCanonical : CanonicalLocalQM31 parent :=
    hweightsCanonical ⟨parentIndex.val, hparentBound⟩
  have hparentExact : qm31ToExact parent = base ⟨parentIndex.val, hparentBound⟩ := by
    change weightsToExact weights ⟨parentIndex.val, hparentBound⟩ = _
    apply hunprocessed
    change parentIndex.val < index.val
    rw [hparentIndex]
    omega
  rcases local_prepared_mul_corresponds prepared localCoordinate parent
      hprepared hcoordinateCanonical hparentCanonical with
    ⟨right, hrightCall, hrightCanonical, hrightExact⟩
  rcases local_qm31_sub_corresponds parent right hparentCanonical hrightCanonical with
    ⟨left, hleftCall, hleftCanonical, hleftExact⟩
  let evenIndex := Std.Usize.wrapping_mul 2#usize parentIndex
  have hevenIndex : evenIndex.val = 2 * parentIndex.val := by
    apply usize_wrapping_mul_two_val
    have hsize : 64 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hplatform | hplatform <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hplatform]
    omega
  have hevenBound : evenIndex.val < 64 := by omega
  have hevenUpdate := weight_update_call weights evenIndex hevenBound left
  let weights1 := weights.set evenIndex left
  let oddIndex := Std.Usize.wrapping_add evenIndex 1#usize
  have hoddIndex : oddIndex.val = evenIndex.val + 1 := by
    apply usize_wrapping_add_one_val
    have hsize : 64 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hplatform | hplatform <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hplatform]
    omega
  have hoddBound : oddIndex.val < 64 := by omega
  have hoddUpdate := weight_update_call weights1 oddIndex hoddBound right
  let weights2 := weights1.set oddIndex right
  have hweights1Canonical : CanonicalLocalWeights weights1 :=
    canonical_weights_set weights evenIndex hevenBound left
      hweightsCanonical hleftCanonical
  have hweights2Canonical : CanonicalLocalWeights weights2 :=
    canonical_weights_set weights1 oddIndex hoddBound right
      hweights1Canonical hrightCanonical
  have hrightMath : qm31ToExact right =
      base ⟨parentIndex.val, hparentBound⟩ * coordinate := by
    rw [hrightExact, hcoordinateExact, hparentExact]
    ring
  have hleftMath : qm31ToExact left =
      base ⟨parentIndex.val, hparentBound⟩ * (1 - coordinate) := by
    rw [hleftExact, hparentExact, hrightMath]
    ring
  have hunprocessed2 : ∀ output : Fin 64, output.val < parentIndex.val →
      weightsToExact weights2 output = base output := by
    intro output houtput
    have hneOdd : oddIndex.val ≠ output.val := by omega
    have hneEven : evenIndex.val ≠ output.val := by omega
    rw [weightsToExact, weightEntry_set_other weights1 oddIndex right output hneOdd]
    rw [weightEntry_set_other weights evenIndex left output hneEven]
    exact hunprocessed output (by omega)
  have hprocessed2 : ∀ output : Fin 64,
      2 * parentIndex.val ≤ output.val → output.val < 2 * width.val →
      weightsToExact weights2 output = ExpandedEntry base coordinate output := by
    intro output hlow hhigh
    by_cases heven : output.val = evenIndex.val
    · have hout : output = ⟨evenIndex.val, hevenBound⟩ := Fin.ext heven
      subst output
      rw [weightsToExact,
        weightEntry_set_other weights1 oddIndex right _ (by omega),
        weightEntry_set_same]
      rw [hleftMath]
      simp [ExpandedEntry, hevenIndex]
    · by_cases hodd : output.val = oddIndex.val
      · have hout : output = ⟨oddIndex.val, hoddBound⟩ := Fin.ext hodd
        subst output
        rw [weightsToExact, weightEntry_set_same]
        rw [hrightMath]
        have hparentFin :
            (⟨parentIndex.val, hparentBound⟩ : Fin 64) =
              ⟨oddIndex.val / 2, by omega⟩ := by
          apply Fin.ext
          change parentIndex.val = oddIndex.val / 2
          omega
        unfold ExpandedEntry
        rw [← hparentFin]
        simp [hoddIndex, hevenIndex]
      · rw [weightsToExact,
          weightEntry_set_other weights1 oddIndex right output (Ne.symm hodd),
          weightEntry_set_other weights evenIndex left output (Ne.symm heven)]
        apply hprocessed output
        omega
        exact hhigh
  let state : LocalWeights × Std.Usize := (weights2, parentIndex)
  have hparentCallLiteral :
      Array.index_usize weights (Std.Usize.wrapping_sub index 1#usize) =
        .ok parent := by
    simpa [parentIndex, parent] using hparentCall
  have hevenUpdateLiteral :
      Array.update weights
          (Std.Usize.wrapping_mul 2#usize
            (Std.Usize.wrapping_sub index 1#usize)) left =
        .ok weights1 := by
    simpa [parentIndex, evenIndex, weights1] using hevenUpdate
  have hoddUpdateLiteral :
      Array.update weights1
          (Std.Usize.wrapping_add
            (Std.Usize.wrapping_mul 2#usize
              (Std.Usize.wrapping_sub index 1#usize)) 1#usize) right =
        .ok weights2 := by
    simpa [parentIndex, evenIndex, oddIndex, weights1, weights2] using hoddUpdate
  refine ⟨state, ?_, hparentIndex, ?_⟩
  · unfold innerBody
    unfold v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights_loop0_loop0.body
    have hcondition : index > 0#usize := by
      apply (UScalar.lt_equiv _ _).2
      change 0 < index.val
      omega
    rw [if_pos hcondition]
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
    rw [hparentCallLiteral]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hrightCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hleftCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hevenUpdateLiteral]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hoddUpdateLiteral]
    simp only [Aeneas.Std.bind_tc_ok]
    simp [state, parentIndex, weights1, weights2]
  · refine ⟨hweights2Canonical, ?_, hwidth,
      hunprocessed2, hprocessed2⟩
    change parentIndex.val ≤ width.val
    rw [hparentIndex]
    omega

private theorem innerBody_done
    (prepared : _root_.aspis_core.field.PreparedQm31Multiplier)
    (weights : LocalWeights) (index : Std.Usize)
    (hzero : index.val = 0) :
    innerBody prepared weights index = .ok (.done weights) := by
  have hcondition : ¬ index > 0#usize := by
    intro hgt
    have hpositive := (UScalar.lt_equiv _ _).1 hgt
    rw [hzero] at hpositive
    exact (Nat.lt_irrefl 0) hpositive
  unfold innerBody
  unfold v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights_loop0_loop0.body
  rw [if_neg hcondition]

theorem innerBody_transition_spec (base : Fin 64 → ExactQM31)
    (coordinate : ExactQM31) (localCoordinate : LocalQM31)
    (prepared : _root_.aspis_core.field.PreparedQm31Multiplier)
    (weights : LocalWeights) (index width : Std.Usize)
    (hcoordinateCanonical : CanonicalLocalQM31 localCoordinate)
    (hcoordinateExact : qm31ToExact localCoordinate = coordinate)
    (hprepared : PreparedFor prepared localCoordinate)
    (hinvariant : InnerInvariant base coordinate weights index width) :
    ∃ flow,
      innerBody prepared weights index = .ok flow ∧
      (match flow with
        | .done result => CanonicalLocalWeights result ∧
            ∀ output : Fin 64, output.val < 2 * width.val →
              weightsToExact result output = ExpandedEntry base coordinate output
        | .cont next =>
            InnerInvariant base coordinate next.1 next.2 width ∧
            next.2.val < index.val) := by
  by_cases hpositive : 1 ≤ index.val
  · rcases innerBody_step base coordinate localCoordinate prepared weights
      index width hcoordinateCanonical hcoordinateExact hprepared hpositive
      hinvariant with ⟨state, hbody, hindex, hstateInvariant⟩
    refine ⟨.cont state, hbody, ?_⟩
    change InnerInvariant base coordinate state.1 state.2 width ∧
      state.2.val < index.val
    exact ⟨hstateInvariant, pred_lt_of_eq_sub_one hpositive hindex⟩
  · have hzero : index.val = 0 := eq_zero_of_not_one_le hpositive
    have hdone := innerBody_done prepared weights index hzero
    refine ⟨.done weights, hdone, hinvariant.1, ?_⟩
    intro output houtput
    apply hinvariant.2.2.2.2 output
    · rw [hzero]
      exact Nat.zero_le output.val
    · exact houtput

theorem innerLoop_spec (base : Fin 64 → ExactQM31)
    (coordinate : ExactQM31) (localCoordinate : LocalQM31)
    (prepared : _root_.aspis_core.field.PreparedQm31Multiplier)
    (weights : LocalWeights) (index width : Std.Usize)
    (hcoordinateCanonical : CanonicalLocalQM31 localCoordinate)
    (hcoordinateExact : qm31ToExact localCoordinate = coordinate)
    (hprepared : PreparedFor prepared localCoordinate)
    (hinvariant : InnerInvariant base coordinate weights index width) :
    ∃ result : LocalWeights,
      innerLoop weights prepared index = .ok result ∧
      CanonicalLocalWeights result ∧
      (∀ output : Fin 64, output.val < 2 * width.val →
        weightsToExact result output =
          ExpandedEntry base coordinate output) := by
  have hspec : Aeneas.Std.WP.spec (innerLoop weights prepared index)
      (fun result => CanonicalLocalWeights result ∧
        ∀ output : Fin 64, output.val < 2 * width.val →
          weightsToExact result output = ExpandedEntry base coordinate output) := by
    unfold innerLoop
    unfold v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights_loop0_loop0
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun state => state.2.val)
      (inv := fun state => InnerInvariant base coordinate state.1 state.2 width)
    · rintro ⟨nextWeights, nextIndex⟩ hstate
      simp only
      apply Aeneas.Std.WP.exists_imp_spec
      have htransition := innerBody_transition_spec base coordinate
        localCoordinate prepared nextWeights nextIndex width
        hcoordinateCanonical hcoordinateExact hprepared hstate
      unfold innerBody at htransition
      rcases htransition with ⟨flow, hcall, hpost⟩
      refine ⟨flow, hcall, ?_⟩
      cases flow <;> exact hpost
    · exact hinvariant
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨result, hcall, hcanonical, hexact⟩
  exact ⟨result, hcall, hcanonical, hexact⟩

def OuterInvariant (point : Fin 10 → ExactQM31)
    (weights : LocalWeights) (width coordinate : Std.Usize) : Prop :=
  CanonicalLocalWeights weights ∧
  3 ≤ coordinate.val ∧ coordinate.val ≤ 9 ∧
  width.val = 2 ^ (coordinate.val - 3) ∧
  (∀ output : Fin 64, output.val < width.val →
    weightsToExact weights output =
      suffixRec point (coordinate.val - 3) output.val)

private abbrev outerBody :=
  v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights_loop0.body

private abbrev outerLoop :=
  v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights_loop0

theorem outerBody_step (point : LocalPoint) (weights : LocalWeights)
    (width coordinate : Std.Usize)
    (hpointCanonical : CanonicalLocalPoint point)
    (hinvariant : OuterInvariant (pointToExact point) weights width coordinate)
    (hcontinue : coordinate.val < 9) :
    ∃ state : LocalWeights × Std.Usize × Std.Usize,
      outerBody point weights width coordinate = .ok (.cont state) ∧
      state.2.2.val = coordinate.val + 1 ∧
      OuterInvariant (pointToExact point) state.1 state.2.1 state.2.2 := by
  rcases hinvariant with
    ⟨hweightsCanonical, hcoordinateLow, hcoordinateHigh,
      hwidth, hweightsExact⟩
  have hcoordinateBound : coordinate.val < 10 := by omega
  have hpointCall := point_index_call point coordinate hcoordinateBound
  let localCoordinate := pointEntry point ⟨coordinate.val, hcoordinateBound⟩
  let exactCoordinate := pointToExact point ⟨coordinate.val, hcoordinateBound⟩
  have hlocalCoordinateCanonical : CanonicalLocalQM31 localCoordinate :=
    hpointCanonical ⟨coordinate.val, hcoordinateBound⟩
  have hlocalCoordinateExact : qm31ToExact localCoordinate = exactCoordinate := rfl
  rcases local_prepared_new_corresponds localCoordinate hlocalCoordinateCanonical with
    ⟨prepared, hpreparedCall, hprepared⟩
  have hwidthBound : width.val ≤ 32 := by
    rw [hwidth]
    interval_cases coordinate.val <;> norm_num
  have hinnerInvariant : InnerInvariant (weightsToExact weights)
      exactCoordinate weights width width := by
    refine ⟨hweightsCanonical, le_rfl, hwidthBound, ?_, ?_⟩
    · intro output _
      rfl
    · intro output hlow hhigh
      omega
  rcases innerLoop_spec (weightsToExact weights) exactCoordinate localCoordinate
      prepared weights width width hlocalCoordinateCanonical
      hlocalCoordinateExact hprepared hinnerInvariant with
    ⟨weights1, hweights1Call, hweights1Canonical, hweights1Exact⟩
  let width1 := Std.Usize.wrapping_mul width 2#usize
  have hwidth1 : width1.val = width.val * 2 := by
    rw [Std.Usize.wrapping_mul_val_eq]
    have htwo : (2#usize : Std.Usize).val = 2 := by rfl
    rw [htwo]
    apply Nat.mod_eq_of_lt
    have hsize : 65 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hplatform | hplatform <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hplatform]
    have hbound : 2 * width.val < Std.Usize.size := by omega
    simpa [Nat.mul_comm] using hbound
  let coordinate1 := Std.Usize.wrapping_add coordinate 1#usize
  have hcoordinate1 : coordinate1.val = coordinate.val + 1 := by
    apply usize_wrapping_add_one_val
    have hsize : 11 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hplatform | hplatform <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hplatform]
    omega
  have hweights1Math : ∀ output : Fin 64, output.val < width1.val →
      weightsToExact weights1 output =
        suffixRec (pointToExact point) (coordinate1.val - 3) output.val := by
    intro output houtput
    have houtput2 : output.val < 2 * width.val := by
      omega
    rw [hweights1Exact output houtput2]
    unfold ExpandedEntry
    have hparent : output.val / 2 < width.val := by
      rw [hwidth1] at houtput
      omega
    rw [hweightsExact ⟨output.val / 2, by omega⟩ hparent]
    rw [hcoordinate1]
    have hcount : coordinate.val + 1 - 3 =
        (coordinate.val - 3) + 1 := by omega
    rw [hcount]
    rw [suffixRec_succ (pointToExact point) (coordinate.val - 3)
      output.val (by omega)]
    unfold exactCoordinate
    have hfin : (⟨3 + (coordinate.val - 3), by omega⟩ : Fin 10) =
        ⟨coordinate.val, hcoordinateBound⟩ := by
      apply Fin.ext
      change 3 + (coordinate.val - 3) = coordinate.val
      omega
    rw [hfin]
  let state : LocalWeights × Std.Usize × Std.Usize :=
    (weights1, width1, coordinate1)
  have hweights1CallLiteral :
      v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights_loop0_loop0
          weights prepared width = .ok weights1 := by
    simpa [innerLoop] using hweights1Call
  refine ⟨state, ?_, hcoordinate1, ?_⟩
  · unfold outerBody
    unfold v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights_loop0.body
    have hcondition : coordinate < 9#usize := by
      apply (UScalar.lt_equiv _ _).2
      change coordinate.val < 9
      exact hcontinue
    rw [if_pos hcondition]
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
    rw [hpointCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hpreparedCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hweights1CallLiteral]
    simp only [Aeneas.Std.bind_tc_ok]
    simp [state, width1, coordinate1]
  · refine ⟨hweights1Canonical, by rw [hcoordinate1]; omega,
      by rw [hcoordinate1]; omega, ?_, hweights1Math⟩
    rw [hwidth1, hwidth, hcoordinate1]
    have hcount : coordinate.val + 1 - 3 =
        (coordinate.val - 3) + 1 := by omega
    rw [hcount, pow_succ]

private theorem outerBody_done (point : LocalPoint) (weights : LocalWeights)
    (width coordinate : Std.Usize) (hfinal : coordinate.val = 9) :
    outerBody point weights width coordinate = .ok (.done weights) := by
  have hcondition : ¬ coordinate < 9#usize := by
    intro hlt
    have hltNat := (UScalar.lt_equiv _ _).1 hlt
    change coordinate.val < 9 at hltNat
    omega
  unfold outerBody
  unfold v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights_loop0.body
  rw [if_neg hcondition]

theorem outerBody_transition_spec (point : LocalPoint)
    (weights : LocalWeights) (width coordinate : Std.Usize)
    (hpointCanonical : CanonicalLocalPoint point)
    (hinvariant : OuterInvariant (pointToExact point) weights width coordinate) :
    ∃ flow,
      outerBody point weights width coordinate = .ok flow ∧
      (match flow with
        | .done result => CanonicalLocalWeights result ∧
            weightsToExact result = exactSuffixWeight (pointToExact point)
        | .cont next =>
            OuterInvariant (pointToExact point) next.1 next.2.1 next.2.2 ∧
            9 - next.2.2.val < 9 - coordinate.val) := by
  by_cases hcontinue : coordinate.val < 9
  · rcases outerBody_step point weights width coordinate hpointCanonical
      hinvariant hcontinue with
      ⟨state, hbody, hcoordinate1, hstateInvariant⟩
    refine ⟨.cont state, hbody, hstateInvariant, ?_⟩
    rw [hcoordinate1]
    omega
  · have hcoordinateFinal : coordinate.val = 9 := by
      rcases hinvariant with ⟨_, _, hupper, _⟩
      omega
    have hdone := outerBody_done point weights width coordinate hcoordinateFinal
    refine ⟨.done weights, hdone, hinvariant.1, ?_⟩
    have hwidthFinal : width.val = 64 := by
      rw [hinvariant.2.2.2.1, hcoordinateFinal]
      norm_num
    funext output
    unfold exactSuffixWeight
    have hactive := hinvariant.2.2.2.2 output (by
      rw [hwidthFinal]
      exact output.isLt)
    rw [hcoordinateFinal] at hactive
    simpa using hactive

theorem outerLoop_spec (point : LocalPoint) (weights : LocalWeights)
    (width coordinate : Std.Usize)
    (hpointCanonical : CanonicalLocalPoint point)
    (hinvariant : OuterInvariant (pointToExact point) weights width coordinate) :
    ∃ result : LocalWeights,
      outerLoop point weights width coordinate = .ok result ∧
      CanonicalLocalWeights result ∧
      weightsToExact result = exactSuffixWeight (pointToExact point) := by
  have hspec : Aeneas.Std.WP.spec
      (outerLoop point weights width coordinate)
      (fun result => CanonicalLocalWeights result ∧
        weightsToExact result = exactSuffixWeight (pointToExact point)) := by
    unfold outerLoop
    unfold v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights_loop0
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun state => 9 - state.2.2.val)
      (inv := fun state => OuterInvariant (pointToExact point)
        state.1 state.2.1 state.2.2)
    · rintro ⟨nextWeights, nextWidth, nextCoordinate⟩ hstate
      simp only
      apply Aeneas.Std.WP.exists_imp_spec
      have htransition := outerBody_transition_spec point nextWeights
        nextWidth nextCoordinate hpointCanonical hstate
      unfold outerBody at htransition
      rcases htransition with ⟨flow, hcall, hpost⟩
      refine ⟨flow, hcall, ?_⟩
      cases flow <;> exact hpost
    · exact hinvariant
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨result, hcall, hcanonical, hexact⟩
  exact ⟨result, hcall, hcanonical, hexact⟩

theorem mle_six_coordinate_suffix_weights_exact_spec (point : LocalPoint)
    (hpointCanonical : CanonicalLocalPoint point) :
    ∃ result : LocalWeights,
      v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights point =
        .ok result ∧
      CanonicalLocalWeights result ∧
      weightsToExact result = exactSuffixWeight (pointToExact point) := by
  have hinitial : OuterInvariant (pointToExact point)
      initialWeights 1#usize 3#usize := by
    refine ⟨initialWeights_canonical, by simp, by simp, by simp, ?_⟩
    intro output houtput
    exact initialWeights_active output houtput
  rcases outerLoop_spec point initialWeights 1#usize 3#usize
      hpointCanonical hinitial with
    ⟨result, hloop, hcanonical, hexact⟩
  refine ⟨result, ?_, hcanonical, hexact⟩
  unfold v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights
  rw [local_zero_call]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [local_one_call]
  simp only [Aeneas.Std.bind_tc_ok]
  have hupdate : Array.update zeroWeights 0#usize oneLocalQM31 =
      .ok initialWeights := by
    exact weight_update_call zeroWeights 0#usize (by simp) oneLocalQM31
  change (do
    let a ← Array.update zeroWeights 0#usize oneLocalQM31
    outerLoop point a 1#usize 3#usize) = .ok result
  rw [hupdate]
  exact hloop

end GoodMatricesCurrent.SourceExtractedTerminalWeights
