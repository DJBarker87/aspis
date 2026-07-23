import GoodMatricesCurrent.SourceExtractedFixedSupport

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedShiftChain

open AspisV5GoodGateSparseShift
open GoodMatricesCurrent.SourceExtractedFixedSupport

private abbrev LocalM31 := aspis_verifier.aspis_core.field.M31
private abbrev ExactM31 := AspisV5ComponentCQM31TowerExact.M31Exact
private abbrev LocalVector := Array LocalM31 48#usize
private abbrev LocalChain := alloc.vec.Vec LocalVector

def singletonChain (value : LocalVector) : LocalChain :=
  ⟨[value], by
    rcases System.Platform.numBits_eq with hplatform | hplatform <;>
      norm_num [Std.Usize.max, Std.Usize.numBits, hplatform]⟩

def ChainEntries (base : Fin 48 → ExactM31) (vectors : LocalChain)
    (limit : Nat) : Prop :=
  vectors.val.length = limit /\
  ∀ step, step < limit →
    Exists fun value : LocalVector =>
      vectors.val[step]? = some value /\
      CanonicalLocalVector value /\
      arrayToExact value = sparseShiftIter step base

def ChainInvariant (base : Fin 48 → ExactM31) (vectors : LocalChain)
    (shifted : LocalVector) (shift : Std.Usize) : Prop :=
  1 ≤ shift.val /\
  shift.val ≤ 12 /\
  ChainEntries base vectors shift.val /\
  CanonicalLocalVector shifted /\
  arrayToExact shifted = sparseShiftIter (shift.val - 1) base /\
  (shift.val ≤ 11 → FixedSupportInput shifted (shift.val - 1))

private abbrev chainLoop :=
  v5_cu_probe.good_gate_probe.good_shifted_directions_loop

private abbrev chainBody :=
  v5_cu_probe.good_gate_probe.good_shifted_directions_loop.body

theorem usize_wrapping_add_one_val (value : Std.Usize)
    (hvalue : value.val + 1 < Std.Usize.size) :
    (Std.Usize.wrapping_add value 1#usize).val = value.val + 1 :=
  GoodMatricesCurrent.SourceExtractedFixedSupport.usize_wrapping_add_one_val
    value hvalue

theorem chainBody_step (base : Fin 48 → ExactM31)
    (vectors : LocalChain) (shifted : LocalVector) (shift : Std.Usize)
    (hcontinueNat : shift.val ≤ 11)
    (hinvariant : ChainInvariant base vectors shifted shift) :
    Exists fun state : LocalChain × LocalVector × Std.Usize =>
      chainBody vectors shifted shift = .ok (.cont state) /\
      state.2.2.val = shift.val + 1 /\
      ChainInvariant base state.1 state.2.1 state.2.2 := by
  rcases hinvariant with
    ⟨hshiftPositive, _hshiftUpper, hentries, hshiftedCanonical,
      hshiftedExact, hshiftedShape⟩
  let shiftMinus := Std.Usize.wrapping_sub shift 1#usize
  have hshiftMinus : shiftMinus.val = shift.val - 1 := by
    unfold shiftMinus
    apply GoodMatricesCurrent.SourceExtractedFixedSupport.usize_wrapping_sub_val_of_le
    simp only [UScalar.ofNatCore_val_eq]
    omega
  have hshape : FixedSupportInput shifted shiftMinus.val := by
    rw [hshiftMinus]
    exact hshiftedShape hcontinueNat
  obtain ⟨shifted1, hshifted1, hshifted1Canonical, hshifted1Exact⟩ :=
    natural_mul_x_fixed_support_exact_spec shifted shiftMinus hshape
  have hvectorsBound : vectors.val.length < Std.Usize.max := by
    rw [hentries.1]
    have hmax : 12 < Std.Usize.max := by
      rcases System.Platform.numBits_eq with hplatform | hplatform <;>
        norm_num [Std.Usize.max, Std.Usize.numBits, hplatform]
    omega
  obtain ⟨vectors1, hvectors1, hvectors1Value⟩ :=
    WP.spec_imp_exists (alloc.vec.Vec.push_spec vectors shifted1 hvectorsBound)
  let shift1 := Std.Usize.wrapping_add shift 1#usize
  have hshift1 : shift1.val = shift.val + 1 := by
    apply usize_wrapping_add_one_val
    have hsize : 13 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hplatform | hplatform <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hplatform]
    omega
  have hentries1 : ChainEntries base vectors1 shift1.val := by
    refine ⟨?_, ?_⟩
    · rw [hvectors1Value, List.length_append, List.length_singleton,
        hentries.1, hshift1]
    · intro step hstep
      rw [hshift1] at hstep
      by_cases hold : step < shift.val
      · obtain ⟨value, hvalue, hvalueCanonical, hvalueExact⟩ :=
          hentries.2 step hold
        refine ⟨value, ?_, hvalueCanonical, hvalueExact⟩
        rw [hvectors1Value, List.getElem?_append_left]
        · exact hvalue
        · simpa [hentries.1] using hold
      · have hnew : step = shift.val := by omega
        subst step
        refine ⟨shifted1, ?_, hshifted1Canonical, ?_⟩
        · rw [hvectors1Value, List.getElem?_append_right]
          · simp [hentries.1]
          · simp [hentries.1]
        · have hpred : shift.val - 1 + 1 = shift.val := by omega
          calc
            arrayToExact shifted1 = sparseShift (arrayToExact shifted) :=
              hshifted1Exact
            _ = sparseShift (sparseShiftIter (shift.val - 1) base) := by
              rw [hshiftedExact]
            _ = sparseShiftIter ((shift.val - 1) + 1) base := rfl
            _ = sparseShiftIter shift.val base := by rw [hpred]
  have hnextInvariant :
      ChainInvariant base vectors1 shifted1 shift1 := by
    refine ⟨by rw [hshift1]; omega, by rw [hshift1]; omega,
      hentries1, hshifted1Canonical, ?_, ?_⟩
    · rw [hshift1]
      have hpred : shift.val + 1 - 1 = shift.val := by omega
      rw [hpred]
      have hpred' : shift.val - 1 + 1 = shift.val := by omega
      calc
        arrayToExact shifted1 = sparseShift (arrayToExact shifted) :=
          hshifted1Exact
        _ = sparseShift (sparseShiftIter (shift.val - 1) base) := by
          rw [hshiftedExact]
        _ = sparseShiftIter ((shift.val - 1) + 1) base := rfl
        _ = sparseShiftIter shift.val base := by rw [hpred']
    · intro hnext
      have hcurrent : shift.val ≤ 10 := by rw [hshift1] at hnext; omega
      have hpreserved := fixedSupportInput_of_exact_sparseShift shifted shifted1
        (shift.val - 1) (by simpa [hshiftMinus] using hshape) (by omega)
        hshifted1Canonical hshifted1Exact
      rw [hshift1]
      have hpred : shift.val - 1 + 1 = shift.val := by omega
      rw [hpred] at hpreserved
      exact hpreserved
  refine ⟨(vectors1, shifted1, shift1), ?_, hshift1, hnextInvariant⟩
  unfold chainBody
  unfold v5_cu_probe.good_gate_probe.good_shifted_directions_loop.body
  simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
  have hcondition : shift <= 11#usize := by
    apply (UScalar.le_equiv _ _).2
    simpa using hcontinueNat
  rw [if_pos hcondition, hshifted1]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hvectors1]

theorem chainLoop_spec (base : Fin 48 → ExactM31)
    (vectors : LocalChain) (shifted : LocalVector) (shift : Std.Usize)
    (hinvariant : ChainInvariant base vectors shifted shift) :
    Exists fun result : LocalChain =>
      chainLoop vectors shifted shift = .ok result /\
      ChainEntries base result 12 := by
  by_cases hcontinueNat : shift.val ≤ 11
  · obtain ⟨state, hbody, hshift1, hstateInvariant⟩ :=
      chainBody_step base vectors shifted shift hcontinueNat hinvariant
    unfold chainBody at hbody
    obtain ⟨result, hresult, hresultEntries⟩ :=
      chainLoop_spec base state.1 state.2.1 state.2.2 hstateInvariant
    unfold chainLoop at hresult
    refine ⟨result, ?_, hresultEntries⟩
    unfold chainLoop
    unfold v5_cu_probe.good_gate_probe.good_shifted_directions_loop
    rw [loop.eq_def]
    simp only
    rw [hbody]
    exact hresult
  · have hfinal : shift.val = 12 := by
      rcases hinvariant with ⟨_, hupper, _⟩
      omega
    have hcondition : ¬ shift <= 11#usize := by
      intro hle
      exact hcontinueNat ((UScalar.le_equiv _ _).1 hle)
    have hbodyDone : chainBody vectors shifted shift = .ok (.done vectors) := by
      unfold chainBody
      unfold v5_cu_probe.good_gate_probe.good_shifted_directions_loop.body
      simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
      rw [if_neg hcondition]
    unfold chainBody at hbodyDone
    refine ⟨vectors, ?_, ?_⟩
    · unfold chainLoop
      unfold v5_cu_probe.good_gate_probe.good_shifted_directions_loop
      rw [loop.eq_def]
      simp only
      rw [hbodyDone]
    · rcases hinvariant with ⟨_, _, hentries, _⟩
      rw [hfinal] at hentries
      exact hentries
termination_by 12 - shift.val
decreasing_by
  rw [hshift1]
  omega

theorem shifted_directions_loop_exact_spec (baseVector : LocalVector)
    (hbaseShape : FixedSupportInput baseVector 0) :
    Exists fun result : LocalChain =>
      chainLoop (singletonChain baseVector) baseVector 1#usize = .ok result /\
      ChainEntries (arrayToExact baseVector) result 12 := by
  let initial : LocalChain := singletonChain baseVector
  have hbaseCanonical : CanonicalLocalVector baseVector := hbaseShape.1
  have hinitialEntries :
      ChainEntries (arrayToExact baseVector) initial 1 := by
    refine ⟨?_, ?_⟩
    · change [baseVector].length = 1
      rfl
    intro step hstep
    have hstepZero : step = 0 := by omega
    subst step
    refine ⟨baseVector, ?_, hbaseCanonical, ?_⟩
    · change [baseVector][0]? = some baseVector
      rfl
    rfl
  have hinitialInvariant :
      ChainInvariant (arrayToExact baseVector) initial baseVector 1#usize := by
    refine ⟨by simp, by simp, hinitialEntries, hbaseCanonical, rfl, ?_⟩
    intro _
    simpa using hbaseShape
  exact chainLoop_spec (arrayToExact baseVector) initial baseVector 1#usize
    hinitialInvariant

end GoodMatricesCurrent.SourceExtractedShiftChain
