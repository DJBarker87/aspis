import GoodMatricesCurrent.ProbeGeneratedConcrete
import GoodMatricesCurrent.SourceExtractedTerminalEvaluator

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.ProbeAbstractDot

open GoodMatricesCurrent.ProbeGeneratedConcrete
open GoodMatricesCurrent.SourceExtractedTerminalField
open GoodMatricesCurrent.SourceExtractedTerminalWeights
open GoodMatricesCurrent.SourceExtractedTerminalEvaluator
open AspisV5GoodGateDotBatching
open AspisV5GoodGateSparseShift

abbrev ExactM31 := AspisV5ComponentCQM31TowerExact.M31Exact

def shiftedExact (shift : Nat) : Fin 48 → ExactM31 :=
  sparseShiftIter shift
    (GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact baseDirection)

theorem sparseShift_even_support (input : Fin 48 → ExactM31)
    (hodd : ∀ index : Fin 48, index.val % 2 ≠ 0 → input index = 0)
    (output : Fin 48) :
    sparseShift input output =
      if h : output.val % 2 ≠ 0 ∧ 0 < output.val then
        input ⟨output.val - 1, by omega⟩
      else 0 := by
  classical
  unfold sparseShift
  simp only [Fintype.linearCombination_apply, Finset.sum_apply]
  split
  next hactive =>
    let source : Fin 47 := ⟨output.val - 1, by omega⟩
    rw [Finset.sum_eq_single source]
    · have hsourceEven : source.val % 2 = 0 := by
        dsimp [source]
        omega
      rw [sparseBasis, if_pos hsourceEven]
      have hsuccessor : successorIndex source = output := by
        apply Fin.ext
        simp [source, successorIndex]
        omega
      rw [hsuccessor]
      simp only [Pi.smul_apply, Pi.single_eq_same, mul_one]
      congr 1
      apply Fin.ext
      simp [sourceIndex, source]
    · intro other _ hne
      by_cases hotherEven : other.val % 2 = 0
      · rw [sparseBasis, if_pos hotherEven]
        have htarget : output ≠ successorIndex other := by
          intro heq
          apply hne
          apply Fin.ext
          have hvalue := congrArg Fin.val heq
          simp [successorIndex, source] at hvalue ⊢
          omega
        simp [Pi.smul_apply, Pi.single_eq_of_ne htarget]
      · rw [hodd (sourceIndex other) (by simpa [sourceIndex] using hotherEven)]
        simp
    · simp
  next hinactive =>
    apply Finset.sum_eq_zero
    intro source _
    by_cases hsourceEven : source.val % 2 = 0
    · rw [sparseBasis, if_pos hsourceEven]
      have htarget : output ≠ successorIndex source := by
        intro heq
        apply hinactive
        constructor
        · have hvalue := congrArg Fin.val heq
          simp [successorIndex] at hvalue
          omega
        · have hvalue := congrArg Fin.val heq
          simp [successorIndex] at hvalue
          omega
      simp [Pi.smul_apply, Pi.single_eq_of_ne htarget]
    · rw [hodd (sourceIndex source) (by simpa [sourceIndex] using hsourceEven)]
      simp

theorem baseDirection_exact_odd_zero (index : Fin 48)
    (hodd : index.val % 2 ≠ 0) :
    GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
      baseDirection index = 0 := by
  fin_cases index <;>
    simp_all [baseDirection, v, Aeneas.Std.Array.make,
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact,
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayEntry,
      GoodMatricesCurrent.SourceExtractedField.m31ToExact]

def direction1Local : GoodMatricesCurrent.ProbeGeneratedConcrete.LocalVector :=
  v [0#u32,1447460119#u32,0#u32,615059998#u32,0#u32,79177021#u32,
    0#u32,264360387#u32,0#u32,175677395#u32,0#u32,690316057#u32,
    0#u32,1940922128#u32,0#u32,1980834973#u32,0#u32,244042458#u32,
    0#u32,1373926702#u32,0#u32,926559219#u32,0#u32,1646207007#u32,
    0#u32,542340637#u32,0#u32,1581685827#u32,0#u32,496267907#u32,
    0#u32,29599140#u32,0#u32,1471327346#u32,0#u32,1038083065#u32,
    0#u32,268435456#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,
    0#u32,0#u32,0#u32,0#u32]

theorem shiftedExact_one :
    shiftedExact 1 =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact direction1Local := by
  funext output
  simp only [shiftedExact, sparseShiftIter]
  rw [sparseShift_even_support _ baseDirection_exact_odd_zero output]
  fin_cases output <;>
    norm_num [direction1Local, baseDirection, v, Aeneas.Std.Array.make,
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact,
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayEntry,
      GoodMatricesCurrent.SourceExtractedField.m31ToExact,
      AspisV5ComponentCQM31TowerExact.P] at *

def evenSource47 (index : Fin 24) : Fin 47 := ⟨2 * index.val, by omega⟩

def oddSource47 (index : Fin 23) : Fin 47 := ⟨2 * index.val + 1, by omega⟩

def paritySourceForward : Fin 24 ⊕ Fin 23 → Fin 47
  | Sum.inl index => evenSource47 index
  | Sum.inr index => oddSource47 index

def paritySourceBackward (index : Fin 47) : Fin 24 ⊕ Fin 23 :=
    if heven : index.val % 2 = 0 then
      Sum.inl ⟨index.val / 2, by omega⟩
    else
      Sum.inr ⟨index.val / 2, by omega⟩

theorem paritySource_left (index : Fin 24 ⊕ Fin 23) :
    paritySourceBackward (paritySourceForward index) = index := by
  rcases index with index | index
  · unfold paritySourceBackward paritySourceForward
    rw [dif_pos (by simp [evenSource47])]
    congr 1
    apply Fin.ext
    simp [evenSource47]
  · unfold paritySourceBackward paritySourceForward
    rw [dif_neg (by simp [oddSource47])]
    congr 1
    apply Fin.ext
    simp [oddSource47]
    omega

theorem paritySource_right (index : Fin 47) :
    paritySourceForward (paritySourceBackward index) = index := by
  unfold paritySourceBackward
  split
  next heven =>
    unfold paritySourceForward
    apply Fin.ext
    simp [evenSource47]
    omega
  next hodd =>
    unfold paritySourceForward
    apply Fin.ext
    simp [oddSource47]
    omega

def paritySourceEquiv : Fin 24 ⊕ Fin 23 ≃ Fin 47 where
  toFun := paritySourceForward
  invFun := paritySourceBackward
  left_inv := paritySource_left
  right_inv := paritySource_right

theorem sparseShift_odd_support (input : Fin 48 → ExactM31)
    (heven : ∀ index : Fin 48, index.val % 2 = 0 → input index = 0) :
    sparseShift input =
      Fintype.linearCombination ExactM31
        (fun index : Fin 23 => sparseBasis (oddSource47 index))
        (fun index : Fin 23 => input (sourceIndex (oddSource47 index))) := by
  classical
  unfold sparseShift
  simp only [Fintype.linearCombination_apply]
  rw [Fintype.sum_equiv paritySourceEquiv.symm
    (fun index : Fin 47 => input (sourceIndex index) • sparseBasis index)
    (fun index : Fin 24 ⊕ Fin 23 =>
      input (sourceIndex (paritySourceEquiv index)) •
        sparseBasis (paritySourceEquiv index)) (by
          intro index
          rw [Equiv.apply_symm_apply])]
  rw [Fintype.sum_sum_type]
  change
    (∑ index : Fin 24,
      input (sourceIndex (evenSource47 index)) • sparseBasis (evenSource47 index)) +
      (∑ index : Fin 23,
        input (sourceIndex (oddSource47 index)) • sparseBasis (oddSource47 index)) =
      ∑ index : Fin 23,
        input (sourceIndex (oddSource47 index)) • sparseBasis (oddSource47 index)
  have hleft :
      (∑ index : Fin 24,
        input (sourceIndex (evenSource47 index)) •
          sparseBasis (evenSource47 index)) =
        (0 : Fin 48 → ExactM31) := by
    apply Finset.sum_eq_zero
    intro index _
    rw [heven (sourceIndex (evenSource47 index)) (by
      simp [sourceIndex, evenSource47])]
    simp
  rw [hleft, zero_add]

def direction2Local : GoodMatricesCurrent.ProbeGeneratedConcrete.LocalVector :=
  v [1706355906#u32,0#u32,2105001882#u32,0#u32,1870056342#u32,0#u32,
    171768704#u32,0#u32,4196220#u32,0#u32,432996726#u32,0#u32,
    564506998#u32,0#u32,887136727#u32,0#u32,1736455008#u32,0#u32,
    808984580#u32,0#u32,681442125#u32,0#u32,1286383113#u32,0#u32,
    70761176#u32,0#u32,1062013232#u32,0#u32,1187826107#u32,0#u32,
    1336675347#u32,0#u32,1801415780#u32,0#u32,180963382#u32,0#u32,
    930609406#u32,0#u32,134217728#u32,0#u32,0#u32,0#u32,0#u32,
    0#u32,0#u32,0#u32,0#u32,0#u32]

theorem direction1_exact_even_zero (index : Fin 48)
    (heven : index.val % 2 = 0) :
    GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
      direction1Local index = 0 := by
  fin_cases index <;>
    simp_all [direction1Local, v, Aeneas.Std.Array.make,
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact,
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayEntry,
      GoodMatricesCurrent.SourceExtractedField.m31ToExact]

def direction1OddCoefficients : Fin 23 → ExactM31 :=
  ![1447460119, 615059998, 79177021, 264360387, 175677395,
    690316057, 1940922128, 1980834973, 244042458, 1373926702,
    926559219, 1646207007, 542340637, 1581685827, 496267907,
    29599140, 1471327346, 1038083065, 268435456, 0, 0, 0, 0]

theorem direction1_odd_coefficients :
    (fun index : Fin 23 =>
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction1Local (sourceIndex (oddSource47 index))) =
      direction1OddCoefficients := by
  funext index
  fin_cases index <;>
    norm_num [direction1OddCoefficients, direction1Local, oddSource47,
      sourceIndex, v, Aeneas.Std.Array.make,
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact,
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayEntry,
      GoodMatricesCurrent.SourceExtractedField.m31ToExact,
      AspisV5ComponentCQM31TowerExact.P]

theorem sum_range_23_chunks {M : Type*} [AddCommMonoid M]
    (term : Nat → M) :
    (∑ index ∈ Finset.range 23, term index) =
      (∑ index ∈ Finset.range 4, term index) +
      (∑ index ∈ Finset.range 4, term (4 + index)) +
      (∑ index ∈ Finset.range 4, term (8 + index)) +
      (∑ index ∈ Finset.range 4, term (12 + index)) +
      (∑ index ∈ Finset.range 4, term (16 + index)) +
      (∑ index ∈ Finset.range 3, term (20 + index)) := by
  rw [show 23 = 4 + 19 by omega, Finset.sum_range_add]
  rw [show 19 = 4 + 15 by omega, Finset.sum_range_add]
  rw [show 15 = 4 + 11 by omega, Finset.sum_range_add]
  rw [show 11 = 4 + 7 by omega, Finset.sum_range_add]
  rw [show 7 = 4 + 3 by omega, Finset.sum_range_add]
  ac_rfl

def oddBasisValue (index : Fin 23) (output : Fin 48) : ExactM31 :=
  let source := oddSource47 index
  let count := trailingOnes source.val
  (if output = successorIndex source then dyadic count else 0) +
    ∑ carry ∈ Finset.range count,
      if output = carryIndex source (carry + 1) then dyadic (carry + 1) else 0

@[simp] theorem exact_inv_two :
    (2 : ExactM31)⁻¹ = (1073741824 : ExactM31) := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

@[simp] theorem exact_inv_four :
    (4 : ExactM31)⁻¹ = (536870912 : ExactM31) := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

@[simp] theorem exact_inv_eight :
    (8 : ExactM31)⁻¹ = (268435456 : ExactM31) := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

@[simp] theorem exact_inv_sixteen :
    (16 : ExactM31)⁻¹ = (134217728 : ExactM31) := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

@[simp] theorem exact_inv_thirtyTwo :
    (32 : ExactM31)⁻¹ = (67108864 : ExactM31) := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

theorem sparseBasis_oddSource47_apply (index : Fin 23) (output : Fin 48) :
    sparseBasis (oddSource47 index) output = oddBasisValue index output := by
  have hodd : (oddSource47 index).val % 2 ≠ 0 := by
    simp [oddSource47]
  rw [sparseBasis, if_neg hodd]
  simp only [Pi.add_apply, Finset.sum_apply]
  simp [oddBasisValue, Pi.single_apply]

theorem oddLinearCombination_apply
    (coefficients : Fin 23 → ExactM31) (output : Fin 48) :
    (Fintype.linearCombination ExactM31
      (fun index : Fin 23 => sparseBasis (oddSource47 index))
      coefficients) output =
      ∑ index : Fin 23, coefficients index * oddBasisValue index output := by
  simp only [Fintype.linearCombination_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro index _
  rw [sparseBasis_oddSource47_apply]

local macro "prove_shift_two_coordinate" : tactic =>
  `(tactic|
    (change sparseShift (shiftedExact 1) _ = _
     rw [shiftedExact_one]
     rw [sparseShift_odd_support _ direction1_exact_even_zero]
     rw [direction1_odd_coefficients]
     rw [oddLinearCombination_apply]
     rw [Finset.sum_fin_eq_sum_range, sum_range_23_chunks]
     simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero]
     conv_rhs =>
       norm_num [direction2Local, v, Aeneas.Std.Array.make,
         GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact,
         GoodMatricesCurrent.SourceExtractedFixedSupport.arrayEntry,
         GoodMatricesCurrent.SourceExtractedField.m31ToExact,
         AspisV5ComponentCQM31TowerExact.P]
     norm_num [Finset.sum_range_succ,
       direction1OddCoefficients, oddSource47, oddBasisValue,
       sourceIndex, successorIndex, carryIndex,
       trailingOnes, dyadic, Pi.single_apply, Fin.ext_iff,
       AspisV5ComponentCQM31TowerExact.P] <;> decide))

theorem shiftedExact_two_0 :
    shiftedExact 2 ⟨0, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨0, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_1 :
    shiftedExact 2 ⟨1, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨1, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_2 :
    shiftedExact 2 ⟨2, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨2, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_3 :
    shiftedExact 2 ⟨3, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨3, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_4 :
    shiftedExact 2 ⟨4, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨4, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_5 :
    shiftedExact 2 ⟨5, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨5, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_6 :
    shiftedExact 2 ⟨6, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨6, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_7 :
    shiftedExact 2 ⟨7, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨7, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_8 :
    shiftedExact 2 ⟨8, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨8, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_9 :
    shiftedExact 2 ⟨9, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨9, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_10 :
    shiftedExact 2 ⟨10, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨10, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_11 :
    shiftedExact 2 ⟨11, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨11, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_12 :
    shiftedExact 2 ⟨12, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨12, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_13 :
    shiftedExact 2 ⟨13, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨13, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_14 :
    shiftedExact 2 ⟨14, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨14, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_15 :
    shiftedExact 2 ⟨15, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨15, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_16 :
    shiftedExact 2 ⟨16, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨16, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_17 :
    shiftedExact 2 ⟨17, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨17, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_18 :
    shiftedExact 2 ⟨18, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨18, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_19 :
    shiftedExact 2 ⟨19, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨19, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_20 :
    shiftedExact 2 ⟨20, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨20, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_21 :
    shiftedExact 2 ⟨21, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨21, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_22 :
    shiftedExact 2 ⟨22, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨22, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_23 :
    shiftedExact 2 ⟨23, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨23, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_24 :
    shiftedExact 2 ⟨24, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨24, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_25 :
    shiftedExact 2 ⟨25, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨25, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_26 :
    shiftedExact 2 ⟨26, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨26, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_27 :
    shiftedExact 2 ⟨27, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨27, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_28 :
    shiftedExact 2 ⟨28, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨28, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_29 :
    shiftedExact 2 ⟨29, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨29, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_30 :
    shiftedExact 2 ⟨30, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨30, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_31 :
    shiftedExact 2 ⟨31, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨31, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_32 :
    shiftedExact 2 ⟨32, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨32, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_33 :
    shiftedExact 2 ⟨33, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨33, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_34 :
    shiftedExact 2 ⟨34, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨34, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_35 :
    shiftedExact 2 ⟨35, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨35, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_36 :
    shiftedExact 2 ⟨36, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨36, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_37 :
    shiftedExact 2 ⟨37, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨37, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_38 :
    shiftedExact 2 ⟨38, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨38, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_39 :
    shiftedExact 2 ⟨39, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨39, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_40 :
    shiftedExact 2 ⟨40, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨40, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_41 :
    shiftedExact 2 ⟨41, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨41, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_42 :
    shiftedExact 2 ⟨42, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨42, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_43 :
    shiftedExact 2 ⟨43, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨43, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_44 :
    shiftedExact 2 ⟨44, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨44, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_45 :
    shiftedExact 2 ⟨45, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨45, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_46 :
    shiftedExact 2 ⟨46, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨46, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two_47 :
    shiftedExact 2 ⟨47, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
        direction2Local ⟨47, by omega⟩ := by
  prove_shift_two_coordinate

theorem shiftedExact_two :
    shiftedExact 2 =
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact direction2Local := by
  funext coordinate
  fin_cases coordinate
  · exact shiftedExact_two_0
  · exact shiftedExact_two_1
  · exact shiftedExact_two_2
  · exact shiftedExact_two_3
  · exact shiftedExact_two_4
  · exact shiftedExact_two_5
  · exact shiftedExact_two_6
  · exact shiftedExact_two_7
  · exact shiftedExact_two_8
  · exact shiftedExact_two_9
  · exact shiftedExact_two_10
  · exact shiftedExact_two_11
  · exact shiftedExact_two_12
  · exact shiftedExact_two_13
  · exact shiftedExact_two_14
  · exact shiftedExact_two_15
  · exact shiftedExact_two_16
  · exact shiftedExact_two_17
  · exact shiftedExact_two_18
  · exact shiftedExact_two_19
  · exact shiftedExact_two_20
  · exact shiftedExact_two_21
  · exact shiftedExact_two_22
  · exact shiftedExact_two_23
  · exact shiftedExact_two_24
  · exact shiftedExact_two_25
  · exact shiftedExact_two_26
  · exact shiftedExact_two_27
  · exact shiftedExact_two_28
  · exact shiftedExact_two_29
  · exact shiftedExact_two_30
  · exact shiftedExact_two_31
  · exact shiftedExact_two_32
  · exact shiftedExact_two_33
  · exact shiftedExact_two_34
  · exact shiftedExact_two_35
  · exact shiftedExact_two_36
  · exact shiftedExact_two_37
  · exact shiftedExact_two_38
  · exact shiftedExact_two_39
  · exact shiftedExact_two_40
  · exact shiftedExact_two_41
  · exact shiftedExact_two_42
  · exact shiftedExact_two_43
  · exact shiftedExact_two_44
  · exact shiftedExact_two_45
  · exact shiftedExact_two_46
  · exact shiftedExact_two_47

def evenVector (coefficients : Fin 24 → ExactM31) : Fin 48 → ExactM31 :=
  fun output =>
    if heven : output.val % 2 = 0 then
      coefficients ⟨output.val / 2, by omega⟩
    else 0

def oddVector (coefficients : Fin 24 → ExactM31) : Fin 48 → ExactM31 :=
  fun output =>
    if hodd : output.val % 2 ≠ 0 then
      coefficients ⟨output.val / 2, by omega⟩
    else 0

def evenCoefficients2 : Fin 24 → ExactM31 :=
  ![1706355906, 2105001882, 1870056342, 171768704, 4196220,
    432996726, 564506998, 887136727, 1736455008, 808984580,
    681442125, 1286383113, 70761176, 1062013232, 1187826107,
    1336675347, 1801415780, 180963382, 930609406, 134217728,
    0, 0, 0, 0]

theorem direction2_exact_evenVector :
    GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact direction2Local =
      evenVector evenCoefficients2 := by
  funext output
  fin_cases output <;>
    norm_num [direction2Local, evenVector, evenCoefficients2,
      v, Aeneas.Std.Array.make,
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact,
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayEntry,
      GoodMatricesCurrent.SourceExtractedField.m31ToExact,
      AspisV5ComponentCQM31TowerExact.P]

theorem shiftedExact_two_evenVector :
    shiftedExact 2 = evenVector evenCoefficients2 := by
  rw [shiftedExact_two, direction2_exact_evenVector]

theorem evenVector_odd_zero (coefficients : Fin 24 → ExactM31)
    (index : Fin 48) (hodd : index.val % 2 ≠ 0) :
    evenVector coefficients index = 0 := by
  simp [evenVector, hodd]

theorem oddVector_even_zero (coefficients : Fin 24 → ExactM31)
    (index : Fin 48) (heven : index.val % 2 = 0) :
    oddVector coefficients index = 0 := by
  simp [oddVector, heven]

theorem sparseShift_evenVector (coefficients : Fin 24 → ExactM31) :
    sparseShift (evenVector coefficients) = oddVector coefficients := by
  funext output
  rw [sparseShift_even_support _ (evenVector_odd_zero coefficients) output]
  fin_cases output <;> norm_num [evenVector, oddVector]

theorem shiftedExact_three :
    shiftedExact 3 = oddVector evenCoefficients2 := by
  change sparseShift (shiftedExact 2) = _
  rw [shiftedExact_two_evenVector, sparseShift_evenVector]

def restrictedOddCoefficients
    (coefficients : Fin 24 → ExactM31) : Fin 23 → ExactM31 :=
  fun index => coefficients index.castSucc

theorem oddVector_source_coefficients (coefficients : Fin 24 → ExactM31) :
    (fun index : Fin 23 =>
      oddVector coefficients (sourceIndex (oddSource47 index))) =
      restrictedOddCoefficients coefficients := by
  funext index
  fin_cases index <;>
    norm_num [oddVector, restrictedOddCoefficients, sourceIndex, oddSource47]

theorem sparseShift_oddVector_apply (coefficients : Fin 24 → ExactM31)
    (output : Fin 48) :
    sparseShift (oddVector coefficients) output =
      ∑ index : Fin 23,
        restrictedOddCoefficients coefficients index *
          oddBasisValue index output := by
  rw [sparseShift_odd_support _ (oddVector_even_zero coefficients)]
  rw [oddVector_source_coefficients]
  exact oddLinearCombination_apply (restrictedOddCoefficients coefficients) output

def evenCoefficients4 : Fin 24 → ExactM31 :=
  ![491483702, 1905678894, 430478994, 1020912523, 1048016838,
    218596473, 1149157774, 1799563686, 833388881, 1272719794,
    327692074, 983912619, 1702508027, 566387204, 1730456110,
    1262250727, 1205823648, 991189581, 1617841804, 532413567,
    16777216, 0, 0, 0]

local macro "prove_shift_four_coordinate" : tactic =>
  `(tactic|
    (rw [sparseShift_oddVector_apply]
     rw [Finset.sum_fin_eq_sum_range, sum_range_23_chunks]
     simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero]
     conv_rhs =>
       norm_num [evenVector, evenCoefficients4]
     norm_num [Finset.sum_range_succ,
       restrictedOddCoefficients, evenCoefficients2,
       oddSource47, oddBasisValue,
       sourceIndex, successorIndex, carryIndex,
       trailingOnes, dyadic, Pi.single_apply, Fin.ext_iff,
       AspisV5ComponentCQM31TowerExact.P] <;> decide))

theorem sparseShift_three_four_0 :
    sparseShift (oddVector evenCoefficients2) ⟨0, by omega⟩ =
      evenVector evenCoefficients4 ⟨0, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_1 :
    sparseShift (oddVector evenCoefficients2) ⟨1, by omega⟩ =
      evenVector evenCoefficients4 ⟨1, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_2 :
    sparseShift (oddVector evenCoefficients2) ⟨2, by omega⟩ =
      evenVector evenCoefficients4 ⟨2, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_3 :
    sparseShift (oddVector evenCoefficients2) ⟨3, by omega⟩ =
      evenVector evenCoefficients4 ⟨3, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_4 :
    sparseShift (oddVector evenCoefficients2) ⟨4, by omega⟩ =
      evenVector evenCoefficients4 ⟨4, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_5 :
    sparseShift (oddVector evenCoefficients2) ⟨5, by omega⟩ =
      evenVector evenCoefficients4 ⟨5, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_6 :
    sparseShift (oddVector evenCoefficients2) ⟨6, by omega⟩ =
      evenVector evenCoefficients4 ⟨6, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_7 :
    sparseShift (oddVector evenCoefficients2) ⟨7, by omega⟩ =
      evenVector evenCoefficients4 ⟨7, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_8 :
    sparseShift (oddVector evenCoefficients2) ⟨8, by omega⟩ =
      evenVector evenCoefficients4 ⟨8, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_9 :
    sparseShift (oddVector evenCoefficients2) ⟨9, by omega⟩ =
      evenVector evenCoefficients4 ⟨9, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_10 :
    sparseShift (oddVector evenCoefficients2) ⟨10, by omega⟩ =
      evenVector evenCoefficients4 ⟨10, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_11 :
    sparseShift (oddVector evenCoefficients2) ⟨11, by omega⟩ =
      evenVector evenCoefficients4 ⟨11, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_12 :
    sparseShift (oddVector evenCoefficients2) ⟨12, by omega⟩ =
      evenVector evenCoefficients4 ⟨12, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_13 :
    sparseShift (oddVector evenCoefficients2) ⟨13, by omega⟩ =
      evenVector evenCoefficients4 ⟨13, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_14 :
    sparseShift (oddVector evenCoefficients2) ⟨14, by omega⟩ =
      evenVector evenCoefficients4 ⟨14, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_15 :
    sparseShift (oddVector evenCoefficients2) ⟨15, by omega⟩ =
      evenVector evenCoefficients4 ⟨15, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_16 :
    sparseShift (oddVector evenCoefficients2) ⟨16, by omega⟩ =
      evenVector evenCoefficients4 ⟨16, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_17 :
    sparseShift (oddVector evenCoefficients2) ⟨17, by omega⟩ =
      evenVector evenCoefficients4 ⟨17, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_18 :
    sparseShift (oddVector evenCoefficients2) ⟨18, by omega⟩ =
      evenVector evenCoefficients4 ⟨18, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_19 :
    sparseShift (oddVector evenCoefficients2) ⟨19, by omega⟩ =
      evenVector evenCoefficients4 ⟨19, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_20 :
    sparseShift (oddVector evenCoefficients2) ⟨20, by omega⟩ =
      evenVector evenCoefficients4 ⟨20, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_21 :
    sparseShift (oddVector evenCoefficients2) ⟨21, by omega⟩ =
      evenVector evenCoefficients4 ⟨21, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_22 :
    sparseShift (oddVector evenCoefficients2) ⟨22, by omega⟩ =
      evenVector evenCoefficients4 ⟨22, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_23 :
    sparseShift (oddVector evenCoefficients2) ⟨23, by omega⟩ =
      evenVector evenCoefficients4 ⟨23, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_24 :
    sparseShift (oddVector evenCoefficients2) ⟨24, by omega⟩ =
      evenVector evenCoefficients4 ⟨24, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_25 :
    sparseShift (oddVector evenCoefficients2) ⟨25, by omega⟩ =
      evenVector evenCoefficients4 ⟨25, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_26 :
    sparseShift (oddVector evenCoefficients2) ⟨26, by omega⟩ =
      evenVector evenCoefficients4 ⟨26, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_27 :
    sparseShift (oddVector evenCoefficients2) ⟨27, by omega⟩ =
      evenVector evenCoefficients4 ⟨27, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_28 :
    sparseShift (oddVector evenCoefficients2) ⟨28, by omega⟩ =
      evenVector evenCoefficients4 ⟨28, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_29 :
    sparseShift (oddVector evenCoefficients2) ⟨29, by omega⟩ =
      evenVector evenCoefficients4 ⟨29, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_30 :
    sparseShift (oddVector evenCoefficients2) ⟨30, by omega⟩ =
      evenVector evenCoefficients4 ⟨30, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_31 :
    sparseShift (oddVector evenCoefficients2) ⟨31, by omega⟩ =
      evenVector evenCoefficients4 ⟨31, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_32 :
    sparseShift (oddVector evenCoefficients2) ⟨32, by omega⟩ =
      evenVector evenCoefficients4 ⟨32, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_33 :
    sparseShift (oddVector evenCoefficients2) ⟨33, by omega⟩ =
      evenVector evenCoefficients4 ⟨33, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_34 :
    sparseShift (oddVector evenCoefficients2) ⟨34, by omega⟩ =
      evenVector evenCoefficients4 ⟨34, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_35 :
    sparseShift (oddVector evenCoefficients2) ⟨35, by omega⟩ =
      evenVector evenCoefficients4 ⟨35, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_36 :
    sparseShift (oddVector evenCoefficients2) ⟨36, by omega⟩ =
      evenVector evenCoefficients4 ⟨36, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_37 :
    sparseShift (oddVector evenCoefficients2) ⟨37, by omega⟩ =
      evenVector evenCoefficients4 ⟨37, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_38 :
    sparseShift (oddVector evenCoefficients2) ⟨38, by omega⟩ =
      evenVector evenCoefficients4 ⟨38, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_39 :
    sparseShift (oddVector evenCoefficients2) ⟨39, by omega⟩ =
      evenVector evenCoefficients4 ⟨39, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_40 :
    sparseShift (oddVector evenCoefficients2) ⟨40, by omega⟩ =
      evenVector evenCoefficients4 ⟨40, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_41 :
    sparseShift (oddVector evenCoefficients2) ⟨41, by omega⟩ =
      evenVector evenCoefficients4 ⟨41, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_42 :
    sparseShift (oddVector evenCoefficients2) ⟨42, by omega⟩ =
      evenVector evenCoefficients4 ⟨42, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_43 :
    sparseShift (oddVector evenCoefficients2) ⟨43, by omega⟩ =
      evenVector evenCoefficients4 ⟨43, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_44 :
    sparseShift (oddVector evenCoefficients2) ⟨44, by omega⟩ =
      evenVector evenCoefficients4 ⟨44, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_45 :
    sparseShift (oddVector evenCoefficients2) ⟨45, by omega⟩ =
      evenVector evenCoefficients4 ⟨45, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_46 :
    sparseShift (oddVector evenCoefficients2) ⟨46, by omega⟩ =
      evenVector evenCoefficients4 ⟨46, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four_47 :
    sparseShift (oddVector evenCoefficients2) ⟨47, by omega⟩ =
      evenVector evenCoefficients4 ⟨47, by omega⟩ := by
  prove_shift_four_coordinate

theorem sparseShift_three_four :
    sparseShift (oddVector evenCoefficients2) =
      evenVector evenCoefficients4 := by
  funext output
  fin_cases output
  · exact sparseShift_three_four_0
  · exact sparseShift_three_four_1
  · exact sparseShift_three_four_2
  · exact sparseShift_three_four_3
  · exact sparseShift_three_four_4
  · exact sparseShift_three_four_5
  · exact sparseShift_three_four_6
  · exact sparseShift_three_four_7
  · exact sparseShift_three_four_8
  · exact sparseShift_three_four_9
  · exact sparseShift_three_four_10
  · exact sparseShift_three_four_11
  · exact sparseShift_three_four_12
  · exact sparseShift_three_four_13
  · exact sparseShift_three_four_14
  · exact sparseShift_three_four_15
  · exact sparseShift_three_four_16
  · exact sparseShift_three_four_17
  · exact sparseShift_three_four_18
  · exact sparseShift_three_four_19
  · exact sparseShift_three_four_20
  · exact sparseShift_three_four_21
  · exact sparseShift_three_four_22
  · exact sparseShift_three_four_23
  · exact sparseShift_three_four_24
  · exact sparseShift_three_four_25
  · exact sparseShift_three_four_26
  · exact sparseShift_three_four_27
  · exact sparseShift_three_four_28
  · exact sparseShift_three_four_29
  · exact sparseShift_three_four_30
  · exact sparseShift_three_four_31
  · exact sparseShift_three_four_32
  · exact sparseShift_three_four_33
  · exact sparseShift_three_four_34
  · exact sparseShift_three_four_35
  · exact sparseShift_three_four_36
  · exact sparseShift_three_four_37
  · exact sparseShift_three_four_38
  · exact sparseShift_three_four_39
  · exact sparseShift_three_four_40
  · exact sparseShift_three_four_41
  · exact sparseShift_three_four_42
  · exact sparseShift_three_four_43
  · exact sparseShift_three_four_44
  · exact sparseShift_three_four_45
  · exact sparseShift_three_four_46
  · exact sparseShift_three_four_47

theorem shiftedExact_four :
    shiftedExact 4 = evenVector evenCoefficients4 := by
  change sparseShift (shiftedExact 3) = _
  rw [shiftedExact_three, sparseShift_three_four]

theorem shiftedExact_five :
    shiftedExact 5 = oddVector evenCoefficients4 := by
  change sparseShift (shiftedExact 4) = _
  rw [shiftedExact_four, sparseShift_evenVector]

def evenCoefficients6 : Fin 24 → ExactM31 :=
  ![
    2008326665, 1198581298, 1483758263, 1799437582, 1736523431,
    1707048479, 542248015, 1474360730, 1451880051, 2126796161,
    1264875052, 1729544170, 736750321, 60705792, 785516626,
    422611595, 1694903754, 24764791, 1189821689, 1385862,
    1953988495, 8388608, 0, 0]

local macro "prove_shift_six_coordinate" : tactic =>
  `(tactic|
    (rw [sparseShift_oddVector_apply]
     rw [Finset.sum_fin_eq_sum_range, sum_range_23_chunks]
     simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero]
     conv_rhs =>
       norm_num [evenVector, evenCoefficients6]
     norm_num [Finset.sum_range_succ,
       restrictedOddCoefficients, evenCoefficients4,
       oddSource47, oddBasisValue,
       sourceIndex, successorIndex, carryIndex,
       trailingOnes, dyadic, Pi.single_apply, Fin.ext_iff,
       AspisV5ComponentCQM31TowerExact.P] <;> decide))

theorem sparseShift_five_six_0 :
    sparseShift (oddVector evenCoefficients4) ⟨0, by omega⟩ =
      evenVector evenCoefficients6 ⟨0, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_1 :
    sparseShift (oddVector evenCoefficients4) ⟨1, by omega⟩ =
      evenVector evenCoefficients6 ⟨1, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_2 :
    sparseShift (oddVector evenCoefficients4) ⟨2, by omega⟩ =
      evenVector evenCoefficients6 ⟨2, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_3 :
    sparseShift (oddVector evenCoefficients4) ⟨3, by omega⟩ =
      evenVector evenCoefficients6 ⟨3, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_4 :
    sparseShift (oddVector evenCoefficients4) ⟨4, by omega⟩ =
      evenVector evenCoefficients6 ⟨4, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_5 :
    sparseShift (oddVector evenCoefficients4) ⟨5, by omega⟩ =
      evenVector evenCoefficients6 ⟨5, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_6 :
    sparseShift (oddVector evenCoefficients4) ⟨6, by omega⟩ =
      evenVector evenCoefficients6 ⟨6, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_7 :
    sparseShift (oddVector evenCoefficients4) ⟨7, by omega⟩ =
      evenVector evenCoefficients6 ⟨7, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_8 :
    sparseShift (oddVector evenCoefficients4) ⟨8, by omega⟩ =
      evenVector evenCoefficients6 ⟨8, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_9 :
    sparseShift (oddVector evenCoefficients4) ⟨9, by omega⟩ =
      evenVector evenCoefficients6 ⟨9, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_10 :
    sparseShift (oddVector evenCoefficients4) ⟨10, by omega⟩ =
      evenVector evenCoefficients6 ⟨10, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_11 :
    sparseShift (oddVector evenCoefficients4) ⟨11, by omega⟩ =
      evenVector evenCoefficients6 ⟨11, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_12 :
    sparseShift (oddVector evenCoefficients4) ⟨12, by omega⟩ =
      evenVector evenCoefficients6 ⟨12, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_13 :
    sparseShift (oddVector evenCoefficients4) ⟨13, by omega⟩ =
      evenVector evenCoefficients6 ⟨13, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_14 :
    sparseShift (oddVector evenCoefficients4) ⟨14, by omega⟩ =
      evenVector evenCoefficients6 ⟨14, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_15 :
    sparseShift (oddVector evenCoefficients4) ⟨15, by omega⟩ =
      evenVector evenCoefficients6 ⟨15, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_16 :
    sparseShift (oddVector evenCoefficients4) ⟨16, by omega⟩ =
      evenVector evenCoefficients6 ⟨16, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_17 :
    sparseShift (oddVector evenCoefficients4) ⟨17, by omega⟩ =
      evenVector evenCoefficients6 ⟨17, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_18 :
    sparseShift (oddVector evenCoefficients4) ⟨18, by omega⟩ =
      evenVector evenCoefficients6 ⟨18, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_19 :
    sparseShift (oddVector evenCoefficients4) ⟨19, by omega⟩ =
      evenVector evenCoefficients6 ⟨19, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_20 :
    sparseShift (oddVector evenCoefficients4) ⟨20, by omega⟩ =
      evenVector evenCoefficients6 ⟨20, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_21 :
    sparseShift (oddVector evenCoefficients4) ⟨21, by omega⟩ =
      evenVector evenCoefficients6 ⟨21, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_22 :
    sparseShift (oddVector evenCoefficients4) ⟨22, by omega⟩ =
      evenVector evenCoefficients6 ⟨22, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_23 :
    sparseShift (oddVector evenCoefficients4) ⟨23, by omega⟩ =
      evenVector evenCoefficients6 ⟨23, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_24 :
    sparseShift (oddVector evenCoefficients4) ⟨24, by omega⟩ =
      evenVector evenCoefficients6 ⟨24, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_25 :
    sparseShift (oddVector evenCoefficients4) ⟨25, by omega⟩ =
      evenVector evenCoefficients6 ⟨25, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_26 :
    sparseShift (oddVector evenCoefficients4) ⟨26, by omega⟩ =
      evenVector evenCoefficients6 ⟨26, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_27 :
    sparseShift (oddVector evenCoefficients4) ⟨27, by omega⟩ =
      evenVector evenCoefficients6 ⟨27, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_28 :
    sparseShift (oddVector evenCoefficients4) ⟨28, by omega⟩ =
      evenVector evenCoefficients6 ⟨28, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_29 :
    sparseShift (oddVector evenCoefficients4) ⟨29, by omega⟩ =
      evenVector evenCoefficients6 ⟨29, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_30 :
    sparseShift (oddVector evenCoefficients4) ⟨30, by omega⟩ =
      evenVector evenCoefficients6 ⟨30, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_31 :
    sparseShift (oddVector evenCoefficients4) ⟨31, by omega⟩ =
      evenVector evenCoefficients6 ⟨31, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_32 :
    sparseShift (oddVector evenCoefficients4) ⟨32, by omega⟩ =
      evenVector evenCoefficients6 ⟨32, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_33 :
    sparseShift (oddVector evenCoefficients4) ⟨33, by omega⟩ =
      evenVector evenCoefficients6 ⟨33, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_34 :
    sparseShift (oddVector evenCoefficients4) ⟨34, by omega⟩ =
      evenVector evenCoefficients6 ⟨34, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_35 :
    sparseShift (oddVector evenCoefficients4) ⟨35, by omega⟩ =
      evenVector evenCoefficients6 ⟨35, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_36 :
    sparseShift (oddVector evenCoefficients4) ⟨36, by omega⟩ =
      evenVector evenCoefficients6 ⟨36, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_37 :
    sparseShift (oddVector evenCoefficients4) ⟨37, by omega⟩ =
      evenVector evenCoefficients6 ⟨37, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_38 :
    sparseShift (oddVector evenCoefficients4) ⟨38, by omega⟩ =
      evenVector evenCoefficients6 ⟨38, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_39 :
    sparseShift (oddVector evenCoefficients4) ⟨39, by omega⟩ =
      evenVector evenCoefficients6 ⟨39, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_40 :
    sparseShift (oddVector evenCoefficients4) ⟨40, by omega⟩ =
      evenVector evenCoefficients6 ⟨40, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_41 :
    sparseShift (oddVector evenCoefficients4) ⟨41, by omega⟩ =
      evenVector evenCoefficients6 ⟨41, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_42 :
    sparseShift (oddVector evenCoefficients4) ⟨42, by omega⟩ =
      evenVector evenCoefficients6 ⟨42, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_43 :
    sparseShift (oddVector evenCoefficients4) ⟨43, by omega⟩ =
      evenVector evenCoefficients6 ⟨43, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_44 :
    sparseShift (oddVector evenCoefficients4) ⟨44, by omega⟩ =
      evenVector evenCoefficients6 ⟨44, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_45 :
    sparseShift (oddVector evenCoefficients4) ⟨45, by omega⟩ =
      evenVector evenCoefficients6 ⟨45, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_46 :
    sparseShift (oddVector evenCoefficients4) ⟨46, by omega⟩ =
      evenVector evenCoefficients6 ⟨46, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six_47 :
    sparseShift (oddVector evenCoefficients4) ⟨47, by omega⟩ =
      evenVector evenCoefficients6 ⟨47, by omega⟩ := by
  prove_shift_six_coordinate

theorem sparseShift_five_six :
    sparseShift (oddVector evenCoefficients4) =
      evenVector evenCoefficients6 := by
  funext output
  fin_cases output
  · exact sparseShift_five_six_0
  · exact sparseShift_five_six_1
  · exact sparseShift_five_six_2
  · exact sparseShift_five_six_3
  · exact sparseShift_five_six_4
  · exact sparseShift_five_six_5
  · exact sparseShift_five_six_6
  · exact sparseShift_five_six_7
  · exact sparseShift_five_six_8
  · exact sparseShift_five_six_9
  · exact sparseShift_five_six_10
  · exact sparseShift_five_six_11
  · exact sparseShift_five_six_12
  · exact sparseShift_five_six_13
  · exact sparseShift_five_six_14
  · exact sparseShift_five_six_15
  · exact sparseShift_five_six_16
  · exact sparseShift_five_six_17
  · exact sparseShift_five_six_18
  · exact sparseShift_five_six_19
  · exact sparseShift_five_six_20
  · exact sparseShift_five_six_21
  · exact sparseShift_five_six_22
  · exact sparseShift_five_six_23
  · exact sparseShift_five_six_24
  · exact sparseShift_five_six_25
  · exact sparseShift_five_six_26
  · exact sparseShift_five_six_27
  · exact sparseShift_five_six_28
  · exact sparseShift_five_six_29
  · exact sparseShift_five_six_30
  · exact sparseShift_five_six_31
  · exact sparseShift_five_six_32
  · exact sparseShift_five_six_33
  · exact sparseShift_five_six_34
  · exact sparseShift_five_six_35
  · exact sparseShift_five_six_36
  · exact sparseShift_five_six_37
  · exact sparseShift_five_six_38
  · exact sparseShift_five_six_39
  · exact sparseShift_five_six_40
  · exact sparseShift_five_six_41
  · exact sparseShift_five_six_42
  · exact sparseShift_five_six_43
  · exact sparseShift_five_six_44
  · exact sparseShift_five_six_45
  · exact sparseShift_five_six_46
  · exact sparseShift_five_six_47

theorem shiftedExact_six :
    shiftedExact 6 = evenVector evenCoefficients6 := by
  change sparseShift (shiftedExact 5) = _
  rw [shiftedExact_five, sparseShift_five_six]

theorem shiftedExact_seven :
    shiftedExact 7 = oddVector evenCoefficients6 := by
  change sparseShift (shiftedExact 6) = _
  rw [shiftedExact_six, sparseShift_evenVector]

def evenCoefficients8 : Fin 24 → ExactM31 :=
  ![
    1030112737, 529712158, 417642028, 567856099, 93635889,
    1721785955, 529605398, 2082046196, 115997850, 1789338106,
    1059651697, 1497209611, 921006535, 1472469880, 2124200395,
    1677805934, 531478600, 1933576096, 64577596, 1669345599,
    1516135544, 2054930375, 2097152, 0]

local macro "prove_shift_eight_coordinate" : tactic =>
  `(tactic|
    (rw [sparseShift_oddVector_apply]
     rw [Finset.sum_fin_eq_sum_range, sum_range_23_chunks]
     simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero]
     conv_rhs =>
       norm_num [evenVector, evenCoefficients8]
     norm_num [Finset.sum_range_succ,
       restrictedOddCoefficients, evenCoefficients6,
       oddSource47, oddBasisValue,
       sourceIndex, successorIndex, carryIndex,
       trailingOnes, dyadic, Pi.single_apply, Fin.ext_iff,
       AspisV5ComponentCQM31TowerExact.P] <;> decide))

theorem sparseShift_seven_eight_0 :
    sparseShift (oddVector evenCoefficients6) ⟨0, by omega⟩ =
      evenVector evenCoefficients8 ⟨0, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_1 :
    sparseShift (oddVector evenCoefficients6) ⟨1, by omega⟩ =
      evenVector evenCoefficients8 ⟨1, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_2 :
    sparseShift (oddVector evenCoefficients6) ⟨2, by omega⟩ =
      evenVector evenCoefficients8 ⟨2, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_3 :
    sparseShift (oddVector evenCoefficients6) ⟨3, by omega⟩ =
      evenVector evenCoefficients8 ⟨3, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_4 :
    sparseShift (oddVector evenCoefficients6) ⟨4, by omega⟩ =
      evenVector evenCoefficients8 ⟨4, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_5 :
    sparseShift (oddVector evenCoefficients6) ⟨5, by omega⟩ =
      evenVector evenCoefficients8 ⟨5, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_6 :
    sparseShift (oddVector evenCoefficients6) ⟨6, by omega⟩ =
      evenVector evenCoefficients8 ⟨6, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_7 :
    sparseShift (oddVector evenCoefficients6) ⟨7, by omega⟩ =
      evenVector evenCoefficients8 ⟨7, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_8 :
    sparseShift (oddVector evenCoefficients6) ⟨8, by omega⟩ =
      evenVector evenCoefficients8 ⟨8, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_9 :
    sparseShift (oddVector evenCoefficients6) ⟨9, by omega⟩ =
      evenVector evenCoefficients8 ⟨9, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_10 :
    sparseShift (oddVector evenCoefficients6) ⟨10, by omega⟩ =
      evenVector evenCoefficients8 ⟨10, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_11 :
    sparseShift (oddVector evenCoefficients6) ⟨11, by omega⟩ =
      evenVector evenCoefficients8 ⟨11, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_12 :
    sparseShift (oddVector evenCoefficients6) ⟨12, by omega⟩ =
      evenVector evenCoefficients8 ⟨12, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_13 :
    sparseShift (oddVector evenCoefficients6) ⟨13, by omega⟩ =
      evenVector evenCoefficients8 ⟨13, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_14 :
    sparseShift (oddVector evenCoefficients6) ⟨14, by omega⟩ =
      evenVector evenCoefficients8 ⟨14, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_15 :
    sparseShift (oddVector evenCoefficients6) ⟨15, by omega⟩ =
      evenVector evenCoefficients8 ⟨15, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_16 :
    sparseShift (oddVector evenCoefficients6) ⟨16, by omega⟩ =
      evenVector evenCoefficients8 ⟨16, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_17 :
    sparseShift (oddVector evenCoefficients6) ⟨17, by omega⟩ =
      evenVector evenCoefficients8 ⟨17, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_18 :
    sparseShift (oddVector evenCoefficients6) ⟨18, by omega⟩ =
      evenVector evenCoefficients8 ⟨18, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_19 :
    sparseShift (oddVector evenCoefficients6) ⟨19, by omega⟩ =
      evenVector evenCoefficients8 ⟨19, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_20 :
    sparseShift (oddVector evenCoefficients6) ⟨20, by omega⟩ =
      evenVector evenCoefficients8 ⟨20, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_21 :
    sparseShift (oddVector evenCoefficients6) ⟨21, by omega⟩ =
      evenVector evenCoefficients8 ⟨21, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_22 :
    sparseShift (oddVector evenCoefficients6) ⟨22, by omega⟩ =
      evenVector evenCoefficients8 ⟨22, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_23 :
    sparseShift (oddVector evenCoefficients6) ⟨23, by omega⟩ =
      evenVector evenCoefficients8 ⟨23, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_24 :
    sparseShift (oddVector evenCoefficients6) ⟨24, by omega⟩ =
      evenVector evenCoefficients8 ⟨24, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_25 :
    sparseShift (oddVector evenCoefficients6) ⟨25, by omega⟩ =
      evenVector evenCoefficients8 ⟨25, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_26 :
    sparseShift (oddVector evenCoefficients6) ⟨26, by omega⟩ =
      evenVector evenCoefficients8 ⟨26, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_27 :
    sparseShift (oddVector evenCoefficients6) ⟨27, by omega⟩ =
      evenVector evenCoefficients8 ⟨27, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_28 :
    sparseShift (oddVector evenCoefficients6) ⟨28, by omega⟩ =
      evenVector evenCoefficients8 ⟨28, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_29 :
    sparseShift (oddVector evenCoefficients6) ⟨29, by omega⟩ =
      evenVector evenCoefficients8 ⟨29, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_30 :
    sparseShift (oddVector evenCoefficients6) ⟨30, by omega⟩ =
      evenVector evenCoefficients8 ⟨30, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_31 :
    sparseShift (oddVector evenCoefficients6) ⟨31, by omega⟩ =
      evenVector evenCoefficients8 ⟨31, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_32 :
    sparseShift (oddVector evenCoefficients6) ⟨32, by omega⟩ =
      evenVector evenCoefficients8 ⟨32, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_33 :
    sparseShift (oddVector evenCoefficients6) ⟨33, by omega⟩ =
      evenVector evenCoefficients8 ⟨33, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_34 :
    sparseShift (oddVector evenCoefficients6) ⟨34, by omega⟩ =
      evenVector evenCoefficients8 ⟨34, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_35 :
    sparseShift (oddVector evenCoefficients6) ⟨35, by omega⟩ =
      evenVector evenCoefficients8 ⟨35, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_36 :
    sparseShift (oddVector evenCoefficients6) ⟨36, by omega⟩ =
      evenVector evenCoefficients8 ⟨36, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_37 :
    sparseShift (oddVector evenCoefficients6) ⟨37, by omega⟩ =
      evenVector evenCoefficients8 ⟨37, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_38 :
    sparseShift (oddVector evenCoefficients6) ⟨38, by omega⟩ =
      evenVector evenCoefficients8 ⟨38, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_39 :
    sparseShift (oddVector evenCoefficients6) ⟨39, by omega⟩ =
      evenVector evenCoefficients8 ⟨39, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_40 :
    sparseShift (oddVector evenCoefficients6) ⟨40, by omega⟩ =
      evenVector evenCoefficients8 ⟨40, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_41 :
    sparseShift (oddVector evenCoefficients6) ⟨41, by omega⟩ =
      evenVector evenCoefficients8 ⟨41, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_42 :
    sparseShift (oddVector evenCoefficients6) ⟨42, by omega⟩ =
      evenVector evenCoefficients8 ⟨42, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_43 :
    sparseShift (oddVector evenCoefficients6) ⟨43, by omega⟩ =
      evenVector evenCoefficients8 ⟨43, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_44 :
    sparseShift (oddVector evenCoefficients6) ⟨44, by omega⟩ =
      evenVector evenCoefficients8 ⟨44, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_45 :
    sparseShift (oddVector evenCoefficients6) ⟨45, by omega⟩ =
      evenVector evenCoefficients8 ⟨45, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_46 :
    sparseShift (oddVector evenCoefficients6) ⟨46, by omega⟩ =
      evenVector evenCoefficients8 ⟨46, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight_47 :
    sparseShift (oddVector evenCoefficients6) ⟨47, by omega⟩ =
      evenVector evenCoefficients8 ⟨47, by omega⟩ := by
  prove_shift_eight_coordinate

theorem sparseShift_seven_eight :
    sparseShift (oddVector evenCoefficients6) =
      evenVector evenCoefficients8 := by
  funext output
  fin_cases output
  · exact sparseShift_seven_eight_0
  · exact sparseShift_seven_eight_1
  · exact sparseShift_seven_eight_2
  · exact sparseShift_seven_eight_3
  · exact sparseShift_seven_eight_4
  · exact sparseShift_seven_eight_5
  · exact sparseShift_seven_eight_6
  · exact sparseShift_seven_eight_7
  · exact sparseShift_seven_eight_8
  · exact sparseShift_seven_eight_9
  · exact sparseShift_seven_eight_10
  · exact sparseShift_seven_eight_11
  · exact sparseShift_seven_eight_12
  · exact sparseShift_seven_eight_13
  · exact sparseShift_seven_eight_14
  · exact sparseShift_seven_eight_15
  · exact sparseShift_seven_eight_16
  · exact sparseShift_seven_eight_17
  · exact sparseShift_seven_eight_18
  · exact sparseShift_seven_eight_19
  · exact sparseShift_seven_eight_20
  · exact sparseShift_seven_eight_21
  · exact sparseShift_seven_eight_22
  · exact sparseShift_seven_eight_23
  · exact sparseShift_seven_eight_24
  · exact sparseShift_seven_eight_25
  · exact sparseShift_seven_eight_26
  · exact sparseShift_seven_eight_27
  · exact sparseShift_seven_eight_28
  · exact sparseShift_seven_eight_29
  · exact sparseShift_seven_eight_30
  · exact sparseShift_seven_eight_31
  · exact sparseShift_seven_eight_32
  · exact sparseShift_seven_eight_33
  · exact sparseShift_seven_eight_34
  · exact sparseShift_seven_eight_35
  · exact sparseShift_seven_eight_36
  · exact sparseShift_seven_eight_37
  · exact sparseShift_seven_eight_38
  · exact sparseShift_seven_eight_39
  · exact sparseShift_seven_eight_40
  · exact sparseShift_seven_eight_41
  · exact sparseShift_seven_eight_42
  · exact sparseShift_seven_eight_43
  · exact sparseShift_seven_eight_44
  · exact sparseShift_seven_eight_45
  · exact sparseShift_seven_eight_46
  · exact sparseShift_seven_eight_47

theorem shiftedExact_eight :
    shiftedExact 8 = evenVector evenCoefficients8 := by
  change sparseShift (shiftedExact 7) = _
  rw [shiftedExact_seven, sparseShift_seven_eight]

theorem shiftedExact_nine :
    shiftedExact 9 = oddVector evenCoefficients8 := by
  change sparseShift (shiftedExact 8) = _
  rw [shiftedExact_eight, sparseShift_evenVector]

def evenCoefficients10 : Fin 24 → ExactM31 :=
  ![
    1035243471, 1853654271, 1020083990, 1566490887, 1076937676,
    907710922, 678889825, 1305825797, 927475411, 952667978,
    814591866, 1278430654, 420191313, 122996384, 1849669151,
    827261341, 1681321599, 1232527348, 396148310, 1940703421,
    675162198, 711791136, 2125393905, 1048576]

local macro "prove_shift_ten_coordinate" : tactic =>
  `(tactic|
    (rw [sparseShift_oddVector_apply]
     rw [Finset.sum_fin_eq_sum_range, sum_range_23_chunks]
     simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero]
     conv_rhs =>
       norm_num [evenVector, evenCoefficients10]
     norm_num [Finset.sum_range_succ,
       restrictedOddCoefficients, evenCoefficients8,
       oddSource47, oddBasisValue,
       sourceIndex, successorIndex, carryIndex,
       trailingOnes, dyadic, Pi.single_apply, Fin.ext_iff,
       AspisV5ComponentCQM31TowerExact.P] <;> decide))

theorem sparseShift_nine_ten_0 :
    sparseShift (oddVector evenCoefficients8) ⟨0, by omega⟩ =
      evenVector evenCoefficients10 ⟨0, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_1 :
    sparseShift (oddVector evenCoefficients8) ⟨1, by omega⟩ =
      evenVector evenCoefficients10 ⟨1, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_2 :
    sparseShift (oddVector evenCoefficients8) ⟨2, by omega⟩ =
      evenVector evenCoefficients10 ⟨2, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_3 :
    sparseShift (oddVector evenCoefficients8) ⟨3, by omega⟩ =
      evenVector evenCoefficients10 ⟨3, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_4 :
    sparseShift (oddVector evenCoefficients8) ⟨4, by omega⟩ =
      evenVector evenCoefficients10 ⟨4, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_5 :
    sparseShift (oddVector evenCoefficients8) ⟨5, by omega⟩ =
      evenVector evenCoefficients10 ⟨5, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_6 :
    sparseShift (oddVector evenCoefficients8) ⟨6, by omega⟩ =
      evenVector evenCoefficients10 ⟨6, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_7 :
    sparseShift (oddVector evenCoefficients8) ⟨7, by omega⟩ =
      evenVector evenCoefficients10 ⟨7, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_8 :
    sparseShift (oddVector evenCoefficients8) ⟨8, by omega⟩ =
      evenVector evenCoefficients10 ⟨8, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_9 :
    sparseShift (oddVector evenCoefficients8) ⟨9, by omega⟩ =
      evenVector evenCoefficients10 ⟨9, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_10 :
    sparseShift (oddVector evenCoefficients8) ⟨10, by omega⟩ =
      evenVector evenCoefficients10 ⟨10, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_11 :
    sparseShift (oddVector evenCoefficients8) ⟨11, by omega⟩ =
      evenVector evenCoefficients10 ⟨11, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_12 :
    sparseShift (oddVector evenCoefficients8) ⟨12, by omega⟩ =
      evenVector evenCoefficients10 ⟨12, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_13 :
    sparseShift (oddVector evenCoefficients8) ⟨13, by omega⟩ =
      evenVector evenCoefficients10 ⟨13, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_14 :
    sparseShift (oddVector evenCoefficients8) ⟨14, by omega⟩ =
      evenVector evenCoefficients10 ⟨14, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_15 :
    sparseShift (oddVector evenCoefficients8) ⟨15, by omega⟩ =
      evenVector evenCoefficients10 ⟨15, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_16 :
    sparseShift (oddVector evenCoefficients8) ⟨16, by omega⟩ =
      evenVector evenCoefficients10 ⟨16, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_17 :
    sparseShift (oddVector evenCoefficients8) ⟨17, by omega⟩ =
      evenVector evenCoefficients10 ⟨17, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_18 :
    sparseShift (oddVector evenCoefficients8) ⟨18, by omega⟩ =
      evenVector evenCoefficients10 ⟨18, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_19 :
    sparseShift (oddVector evenCoefficients8) ⟨19, by omega⟩ =
      evenVector evenCoefficients10 ⟨19, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_20 :
    sparseShift (oddVector evenCoefficients8) ⟨20, by omega⟩ =
      evenVector evenCoefficients10 ⟨20, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_21 :
    sparseShift (oddVector evenCoefficients8) ⟨21, by omega⟩ =
      evenVector evenCoefficients10 ⟨21, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_22 :
    sparseShift (oddVector evenCoefficients8) ⟨22, by omega⟩ =
      evenVector evenCoefficients10 ⟨22, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_23 :
    sparseShift (oddVector evenCoefficients8) ⟨23, by omega⟩ =
      evenVector evenCoefficients10 ⟨23, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_24 :
    sparseShift (oddVector evenCoefficients8) ⟨24, by omega⟩ =
      evenVector evenCoefficients10 ⟨24, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_25 :
    sparseShift (oddVector evenCoefficients8) ⟨25, by omega⟩ =
      evenVector evenCoefficients10 ⟨25, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_26 :
    sparseShift (oddVector evenCoefficients8) ⟨26, by omega⟩ =
      evenVector evenCoefficients10 ⟨26, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_27 :
    sparseShift (oddVector evenCoefficients8) ⟨27, by omega⟩ =
      evenVector evenCoefficients10 ⟨27, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_28 :
    sparseShift (oddVector evenCoefficients8) ⟨28, by omega⟩ =
      evenVector evenCoefficients10 ⟨28, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_29 :
    sparseShift (oddVector evenCoefficients8) ⟨29, by omega⟩ =
      evenVector evenCoefficients10 ⟨29, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_30 :
    sparseShift (oddVector evenCoefficients8) ⟨30, by omega⟩ =
      evenVector evenCoefficients10 ⟨30, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_31 :
    sparseShift (oddVector evenCoefficients8) ⟨31, by omega⟩ =
      evenVector evenCoefficients10 ⟨31, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_32 :
    sparseShift (oddVector evenCoefficients8) ⟨32, by omega⟩ =
      evenVector evenCoefficients10 ⟨32, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_33 :
    sparseShift (oddVector evenCoefficients8) ⟨33, by omega⟩ =
      evenVector evenCoefficients10 ⟨33, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_34 :
    sparseShift (oddVector evenCoefficients8) ⟨34, by omega⟩ =
      evenVector evenCoefficients10 ⟨34, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_35 :
    sparseShift (oddVector evenCoefficients8) ⟨35, by omega⟩ =
      evenVector evenCoefficients10 ⟨35, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_36 :
    sparseShift (oddVector evenCoefficients8) ⟨36, by omega⟩ =
      evenVector evenCoefficients10 ⟨36, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_37 :
    sparseShift (oddVector evenCoefficients8) ⟨37, by omega⟩ =
      evenVector evenCoefficients10 ⟨37, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_38 :
    sparseShift (oddVector evenCoefficients8) ⟨38, by omega⟩ =
      evenVector evenCoefficients10 ⟨38, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_39 :
    sparseShift (oddVector evenCoefficients8) ⟨39, by omega⟩ =
      evenVector evenCoefficients10 ⟨39, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_40 :
    sparseShift (oddVector evenCoefficients8) ⟨40, by omega⟩ =
      evenVector evenCoefficients10 ⟨40, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_41 :
    sparseShift (oddVector evenCoefficients8) ⟨41, by omega⟩ =
      evenVector evenCoefficients10 ⟨41, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_42 :
    sparseShift (oddVector evenCoefficients8) ⟨42, by omega⟩ =
      evenVector evenCoefficients10 ⟨42, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_43 :
    sparseShift (oddVector evenCoefficients8) ⟨43, by omega⟩ =
      evenVector evenCoefficients10 ⟨43, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_44 :
    sparseShift (oddVector evenCoefficients8) ⟨44, by omega⟩ =
      evenVector evenCoefficients10 ⟨44, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_45 :
    sparseShift (oddVector evenCoefficients8) ⟨45, by omega⟩ =
      evenVector evenCoefficients10 ⟨45, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_46 :
    sparseShift (oddVector evenCoefficients8) ⟨46, by omega⟩ =
      evenVector evenCoefficients10 ⟨46, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten_47 :
    sparseShift (oddVector evenCoefficients8) ⟨47, by omega⟩ =
      evenVector evenCoefficients10 ⟨47, by omega⟩ := by
  prove_shift_ten_coordinate

theorem sparseShift_nine_ten :
    sparseShift (oddVector evenCoefficients8) =
      evenVector evenCoefficients10 := by
  funext output
  fin_cases output
  · exact sparseShift_nine_ten_0
  · exact sparseShift_nine_ten_1
  · exact sparseShift_nine_ten_2
  · exact sparseShift_nine_ten_3
  · exact sparseShift_nine_ten_4
  · exact sparseShift_nine_ten_5
  · exact sparseShift_nine_ten_6
  · exact sparseShift_nine_ten_7
  · exact sparseShift_nine_ten_8
  · exact sparseShift_nine_ten_9
  · exact sparseShift_nine_ten_10
  · exact sparseShift_nine_ten_11
  · exact sparseShift_nine_ten_12
  · exact sparseShift_nine_ten_13
  · exact sparseShift_nine_ten_14
  · exact sparseShift_nine_ten_15
  · exact sparseShift_nine_ten_16
  · exact sparseShift_nine_ten_17
  · exact sparseShift_nine_ten_18
  · exact sparseShift_nine_ten_19
  · exact sparseShift_nine_ten_20
  · exact sparseShift_nine_ten_21
  · exact sparseShift_nine_ten_22
  · exact sparseShift_nine_ten_23
  · exact sparseShift_nine_ten_24
  · exact sparseShift_nine_ten_25
  · exact sparseShift_nine_ten_26
  · exact sparseShift_nine_ten_27
  · exact sparseShift_nine_ten_28
  · exact sparseShift_nine_ten_29
  · exact sparseShift_nine_ten_30
  · exact sparseShift_nine_ten_31
  · exact sparseShift_nine_ten_32
  · exact sparseShift_nine_ten_33
  · exact sparseShift_nine_ten_34
  · exact sparseShift_nine_ten_35
  · exact sparseShift_nine_ten_36
  · exact sparseShift_nine_ten_37
  · exact sparseShift_nine_ten_38
  · exact sparseShift_nine_ten_39
  · exact sparseShift_nine_ten_40
  · exact sparseShift_nine_ten_41
  · exact sparseShift_nine_ten_42
  · exact sparseShift_nine_ten_43
  · exact sparseShift_nine_ten_44
  · exact sparseShift_nine_ten_45
  · exact sparseShift_nine_ten_46
  · exact sparseShift_nine_ten_47

theorem shiftedExact_ten :
    shiftedExact 10 = evenVector evenCoefficients10 := by
  change sparseShift (shiftedExact 9) = _
  rw [shiftedExact_nine, sparseShift_nine_ten]

theorem shiftedExact_eleven :
    shiftedExact 11 = oddVector evenCoefficients10 := by
  change sparseShift (shiftedExact 10) = _
  rw [shiftedExact_ten, sparseShift_evenVector]


def exactWeightWord (index limb : Nat) : ExactM31 :=
  if hindex : index < 64 then
    if hlimb : limb < 4 then
      exactQM31Limb (weightsToExact weights ⟨index, hindex⟩) ⟨limb, hlimb⟩
    else 0
  else 0

def exactLiveDot (shift : Fin 12) (mask limb : Nat) : ExactM31 :=
  ∑ logical ∈ Finset.range (19 + shift.val / 2),
    if hindex : shift.val % 2 + 2 * logical < 48 then
      shiftedExact shift.val ⟨shift.val % 2 + 2 * logical, hindex⟩ *
        exactWeightWord (Nat.xor (shift.val % 2 + 2 * logical) mask) limb
    else 0

example : exactLiveDot (1 : Fin 12) 0 0 = (748609204 : ExactM31) := by
  simp only [exactLiveDot]
  change (∑ logical ∈ Finset.range 19,
    if hindex : 1 + 2 * logical < 48 then
      shiftedExact 1 ⟨1 + 2 * logical, hindex⟩ *
        exactWeightWord (Nat.xor (1 + 2 * logical) 0) 0
    else 0) = _
  rw [shiftedExact_one]
  norm_num [
    GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact,
    GoodMatricesCurrent.SourceExtractedFixedSupport.arrayEntry,
    direction1Local, baseDirection, v, Aeneas.Std.Array.make, exactWeightWord,
    weightsToExact, weightEntry, weights, q, qm31ToExact, cm31ToExact,
    exactQM31Limb, sparseShift, sparseBasis, sourceIndex, successorIndex,
    Fintype.linearCombination_apply, Fin.sum_univ_succ,
    Finset.sum_range_succ, Pi.single_apply, Fin.ext_iff, carryIndex,
    trailingOnes, dyadic, GoodMatricesCurrent.SourceExtractedField.m31ToExact,
    AspisV5ComponentCQM31TowerExact.P] <;> decide

end GoodMatricesCurrent.ProbeAbstractDot
