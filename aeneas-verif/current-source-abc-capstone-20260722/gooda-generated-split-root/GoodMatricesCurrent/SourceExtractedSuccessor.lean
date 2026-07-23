import GoodMatricesCurrent.SourceExtractedTerminalFieldAll
import AspisFormal.V5ComponentADeployedTerminalApplicability

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedSuccessor

open GoodMatricesCurrent.SourceExtractedTerminalField
open AspisV5ComponentADeployedTerminalApplicability

abbrev LocalPoint := Array LocalQM31 10#usize

def pointEntry (point : LocalPoint) (index : Fin 10) : LocalQM31 :=
  point.val[index.val]'(by rw [point.property]; exact index.isLt)

def pointToExact (point : LocalPoint) : Fin 10 → ExactQM31 :=
  fun index => qm31ToExact (pointEntry point index)

def CanonicalLocalPoint (point : LocalPoint) : Prop :=
  ∀ index : Fin 10, CanonicalLocalQM31 (pointEntry point index)

@[simp] theorem pointEntry_set_same (point : LocalPoint)
    (index : Std.Usize) (hindex : index.val < 10) (value : LocalQM31) :
    pointEntry (point.set index value) ⟨index.val, hindex⟩ = value := by
  unfold pointEntry
  exact List.getElem_set_self (by
    simp only [List.length_set]
    rw [point.property]
    exact hindex)

@[simp] theorem pointEntry_set_other (point : LocalPoint)
    (index : Std.Usize) (value : LocalQM31) (output : Fin 10)
    (hne : index.val ≠ output.val) :
    pointEntry (point.set index value) output = pointEntry point output := by
  unfold pointEntry
  exact List.getElem_set_ne hne (by
    simp only [List.length_set]
    rw [point.property]
    exact output.isLt)

theorem canonical_point_set (point : LocalPoint)
    (index : Std.Usize) (hindex : index.val < 10) (value : LocalQM31)
    (hpoint : CanonicalLocalPoint point)
    (hvalue : CanonicalLocalQM31 value) :
    CanonicalLocalPoint (point.set index value) := by
  intro output
  by_cases heq : index.val = output.val
  · have hout : output = ⟨index.val, hindex⟩ := Fin.ext heq.symm
    subst output
    simpa using hvalue
  · rw [pointEntry_set_other point index value output heq]
    exact hpoint output

theorem point_index_call (point : LocalPoint) (index : Std.Usize)
    (hindex : index.val < 10) :
    Array.index_usize point index =
      .ok (pointEntry point ⟨index.val, hindex⟩) := by
  exact Array.index_usize_eq_ok_of_getElem_eq point index
    (by rw [point.property]; exact hindex) _ rfl

theorem point_update_call (point : LocalPoint) (index : Std.Usize)
    (hindex : index.val < 10) (value : LocalQM31) :
    Array.update point index value = .ok (point.set index value) := by
  exact Array.update_eq_ok _ _ _ (by rw [point.property]; exact hindex)


def zeroLocalQM31 : LocalQM31 :=
  { c0 := { a := 0#u32, b := 0#u32 },
    c1 := { a := 0#u32, b := 0#u32 } }

def oneLocalQM31 : LocalQM31 :=
  { c0 := { a := 1#u32, b := 0#u32 },
    c1 := { a := 0#u32, b := 0#u32 } }

def zeroPoint : LocalPoint := Array.repeat 10#usize zeroLocalQM31

theorem zeroPoint_canonical : CanonicalLocalPoint zeroPoint := by
  intro index
  unfold pointEntry zeroPoint
  simpa only [Array.repeat_val, List.getElem_replicate,
    zeroLocalQM31] using local_zero_canonical

def tailProduct (point : Fin 10 → ExactQM31) (coordinate : Nat) : ExactQM31 :=
  ∏ output : Fin 10, if coordinate ≤ output.val then point output else 1

def sourceSuccessor (point : Fin 10 → ExactQM31) (coordinate : Fin 10) :
    ExactQM31 :=
  let carry := tailProduct point (coordinate.val + 1)
  let product := point coordinate * carry
  point coordinate + carry - (product + product)

theorem tailProduct_ten (point : Fin 10 → ExactQM31) :
    tailProduct point 10 = 1 := by
  simp [tailProduct, Fin.prod_univ_succ]

theorem tailProduct_step (point : Fin 10 → ExactQM31) (coordinate : Nat)
    (hlow : 1 ≤ coordinate) (hhigh : coordinate ≤ 10) :
    tailProduct point (coordinate - 1) =
      point ⟨coordinate - 1, by omega⟩ * tailProduct point coordinate := by
  interval_cases coordinate <;>
    simp [tailProduct, Fin.prod_univ_succ] <;> ring

theorem tailProduct_successorCarry (point : Fin 10 → ExactQM31)
    (coordinate : Fin 10) :
    tailProduct point (coordinate.val + 1) = successorCarry point coordinate := by
  classical
  unfold tailProduct successorCarry
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro output _
  have hequiv : coordinate.val + 1 ≤ output.val ↔ coordinate < output := by
    change coordinate.val + 1 ≤ output.val ↔ coordinate.val < output.val
    omega
  rw [if_congr hequiv rfl rfl]

theorem sourceSuccessor_eq_deployed (point : Fin 10 → ExactQM31) :
    sourceSuccessor point = deployedSuccessorPoint point := by
  funext coordinate
  unfold sourceSuccessor deployedSuccessorPoint
  rw [tailProduct_successorCarry]

def SuccessorInvariant (point : Fin 10 → ExactQM31)
    (successor : LocalPoint) (carry : LocalQM31)
    (coordinate : Std.Usize) : Prop :=
  CanonicalLocalPoint successor ∧ CanonicalLocalQM31 carry ∧
  coordinate.val ≤ 10 ∧
  qm31ToExact carry = tailProduct point coordinate.val ∧
  ∀ output : Fin 10, coordinate.val ≤ output.val →
    pointToExact successor output = sourceSuccessor point output

private abbrev successorBody :=
  v5_cu_probe.good_gate_probe.binary_successor_point_loop.body

private abbrev successorLoop :=
  v5_cu_probe.good_gate_probe.binary_successor_point_loop

theorem usize_wrapping_sub_one_val (coordinate : Std.Usize)
    (hpositive : 1 ≤ coordinate.val) :
    (Std.Usize.wrapping_sub coordinate 1#usize).val = coordinate.val - 1 := by
  rw [Std.Usize.wrapping_sub_val_eq]
  have hone : (1#usize : Std.Usize).val = 1 := by rfl
  rw [hone]
  have hcoordinate := coordinate.hSize
  have hrearrange :
      coordinate.val + (UScalar.size .Usize - 1) =
        (coordinate.val - 1) + UScalar.size .Usize := by omega
  rw [hrearrange, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem successorBody_step (point successor : LocalPoint)
    (carry : LocalQM31) (coordinate : Std.Usize)
    (hpoint : CanonicalLocalPoint point)
    (hinvariant : SuccessorInvariant (pointToExact point)
      successor carry coordinate)
    (hpositive : 1 ≤ coordinate.val) :
    ∃ state : LocalPoint × LocalQM31 × Std.Usize,
      successorBody point successor carry coordinate = .ok (.cont state) ∧
      state.2.2.val = coordinate.val - 1 ∧
      SuccessorInvariant (pointToExact point) state.1 state.2.1 state.2.2 := by
  rcases hinvariant with
    ⟨hsuccessorCanonical, hcarryCanonical, hcoordinate,
      hcarryExact, hsuccessorExact⟩
  let coordinate1 := Std.Usize.wrapping_sub coordinate 1#usize
  have hcoordinate1 : coordinate1.val = coordinate.val - 1 :=
    usize_wrapping_sub_one_val coordinate hpositive
  have hcoordinate1Bound : coordinate1.val < 10 := by omega
  let value := pointEntry point ⟨coordinate1.val, hcoordinate1Bound⟩
  have hvalueCall : Array.index_usize point coordinate1 = .ok value := by
    simpa [value] using
      point_index_call point coordinate1 hcoordinate1Bound
  have hvalueCanonical : CanonicalLocalQM31 value :=
    hpoint ⟨coordinate1.val, hcoordinate1Bound⟩
  have hvalueExact : qm31ToExact value =
      pointToExact point ⟨coordinate1.val, hcoordinate1Bound⟩ := by
    rfl
  rcases local_qm31_mul_corresponds value carry
      hvalueCanonical hcarryCanonical with
    ⟨valueTimesCarry, hmulCall, hmulCanonical, hmulExact⟩
  rcases local_qm31_add_corresponds value carry
      hvalueCanonical hcarryCanonical with
    ⟨sum, hsumCall, hsumCanonical, hsumExact⟩
  rcases local_qm31_add_corresponds valueTimesCarry valueTimesCarry
      hmulCanonical hmulCanonical with
    ⟨doubleProduct, hdoubleCall, hdoubleCanonical, hdoubleExact⟩
  rcases local_qm31_sub_corresponds sum doubleProduct
      hsumCanonical hdoubleCanonical with
    ⟨nextValue, hsubCall, hnextCanonical, hnextExact⟩
  have hupdateCall := point_update_call successor coordinate1
    hcoordinate1Bound nextValue
  let successor1 := successor.set coordinate1 nextValue
  have hsuccessor1Canonical : CanonicalLocalPoint successor1 :=
    canonical_point_set successor coordinate1 hcoordinate1Bound nextValue
      hsuccessorCanonical hnextCanonical
  have hcoordinateFin :
      (⟨coordinate1.val, hcoordinate1Bound⟩ : Fin 10) =
        ⟨coordinate.val - 1, by omega⟩ := by
    apply Fin.ext
    exact hcoordinate1
  have hnewCarryExact : qm31ToExact valueTimesCarry =
      tailProduct (pointToExact point) coordinate1.val := by
    rw [hmulExact, hcarryExact, hcoordinate1]
    rw [tailProduct_step (pointToExact point) coordinate.val hpositive hcoordinate]
    rw [← hcoordinateFin]
    rw [hvalueExact]
  have hnextValueExact : qm31ToExact nextValue =
      sourceSuccessor (pointToExact point)
        ⟨coordinate1.val, hcoordinate1Bound⟩ := by
    rw [hnextExact, hsumExact, hdoubleExact, hmulExact, hcarryExact]
    unfold sourceSuccessor
    have htail : tailProduct (pointToExact point) coordinate.val =
        tailProduct (pointToExact point) (coordinate1.val + 1) := by
      rw [hcoordinate1]
      congr 1
      omega
    rw [htail, hvalueExact]
  have hsuccessor1Exact : ∀ output : Fin 10,
      coordinate1.val ≤ output.val →
      pointToExact successor1 output =
        sourceSuccessor (pointToExact point) output := by
    intro output houtput
    by_cases heq : coordinate1.val = output.val
    · have hout : output = ⟨coordinate1.val, hcoordinate1Bound⟩ :=
        Fin.ext heq.symm
      subst output
      rw [pointToExact]
      unfold successor1
      rw [pointEntry_set_same]
      exact hnextValueExact
    · rw [pointToExact,
        pointEntry_set_other successor coordinate1 nextValue output heq]
      exact hsuccessorExact output (by omega)
  let state : LocalPoint × LocalQM31 × Std.Usize :=
    (successor1, valueTimesCarry, coordinate1)
  have hvalueCallLiteral :
      Array.index_usize point
          (Std.Usize.wrapping_sub coordinate 1#usize) = .ok value := by
    simpa [coordinate1] using hvalueCall
  have hupdateCallLiteral :
      Array.update successor
          (Std.Usize.wrapping_sub coordinate 1#usize) nextValue =
        .ok successor1 := by
    simpa [coordinate1, successor1] using hupdateCall
  refine ⟨state, ?_, ?_, ?_⟩
  · unfold successorBody
    unfold v5_cu_probe.good_gate_probe.binary_successor_point_loop.body
    have hcondition : coordinate > 0#usize := by
      apply (UScalar.lt_equiv _ _).2
      change 0 < coordinate.val
      omega
    rw [if_pos hcondition]
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
    rw [hvalueCallLiteral]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hmulCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hsumCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hdoubleCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hsubCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hupdateCallLiteral]
    simp only [Aeneas.Std.bind_tc_ok]
    simpa [state, coordinate1, successor1]
  · change coordinate1.val = coordinate.val - 1
    exact hcoordinate1
  · change SuccessorInvariant (pointToExact point)
      successor1 valueTimesCarry coordinate1
    exact ⟨hsuccessor1Canonical, hmulCanonical, by omega,
      hnewCarryExact, hsuccessor1Exact⟩

end GoodMatricesCurrent.SourceExtractedSuccessor
