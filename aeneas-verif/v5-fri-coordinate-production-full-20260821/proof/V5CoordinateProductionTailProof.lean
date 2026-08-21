import V5CoordinateProductionFullProof
import V5FriBatchInverseMathematics

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 28000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CoordinateProductionTailProof

open V5CoordinateProductionFullProof
open V5CoordinateSelectedProductionProof
open AspisV5FriArithmeticSemantics
open AspisV5FriCoordinateFieldSemantics
open AspisV5FriBatchInverseMathematics
open AspisV5FriCoordinateInverseLoops
open AspisCircleGroupOrder
open AspisV5FriCoordinateReleasedPointConnection

namespace Source
open V5CoordinateSelectedProductionSource
end Source

open V5CoordinateSelectedProductionSource

abbrev M31 := V5CoordinateSelectedProductionSource.field.M31
abbrev M31Vec := alloc.vec.Vec M31
abbrev Point := V5CoordinateSelectedProductionSource.circle_fri.BaseCirclePoint
abbrev PointVec := alloc.vec.Vec Point
abbrev Output :=
  V5CoordinateSelectedProductionSource.circle_fri.DerivedCircleQueryFoldInverses

instance : Inhabited M31 := ⟨0#u32⟩
instance : Inhabited Point := ⟨{ x := 0#u32, y := 0#u32 }⟩

/-- If one unfolded loop step obtains its final result from another `Result`
computation and immediately returns it, acceptance of the loop is exactly
acceptance of that computation.  This is the small result-aware inversion
used at the two generated loop-wrapper boundaries below. -/
private theorem source_loop_terminal_accepted
    {State Output : Type}
    (body : State → Result (ControlFlow State Output))
    (state : State) (terminal : Result Output) (result : Output)
    (hbody : body state = do
      let value ← terminal
      .ok (.done value))
    (haccepted : loop body state = .ok result) :
    terminal = .ok result := by
  rw [loop.eq_def, hbody] at haccepted
  cases hterminal : terminal <;> simp [hterminal] at haccepted ⊢
  exact haccepted

private theorem getElemBang_eq_getElem {T : Type*} [Inhabited T]
    (values : List T) (index : Nat) (hindex : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem getElemBang_append_left {T : Type*} [Inhabited T]
    (head tail : List T) (index : Nat) (hindex : index < head.length) :
    (head ++ tail)[index]! = head[index]! := by
  have happ : index < (head ++ tail).length := by
    simp only [List.length_append]
    omega
  rw [getElemBang_eq_getElem _ _ happ,
    List.getElem_append_left hindex,
    ← getElemBang_eq_getElem head index hindex]

/-- The checked operations in the unchanged reducer are in range for every
U64 input, so they agree with the wrapping spelling used by the proof adapter. -/
theorem source_reduce_u64_eq_adapter_arbitrary (value : Std.U64) :
    V5CoordinateSelectedProductionSource.field.reduce_u64 value =
      V5FriCoordinateAdapter.aspis_core.field.reduce_u64 value := by
  unfold V5CoordinateSelectedProductionSource.field.reduce_u64
    V5FriCoordinateAdapter.aspis_core.field.reduce_u64
  rw [p_eq]
  have hmask :
      (UScalar.cast .U64
        V5FriCoordinateAdapter.aspis_core.field.P).val = 2147483647 := by
    rw [Std.U32.cast_U64_val_eq, adapter_p_val_eq]
  have hvalueMax : value.val ≤ 18446744073709551615 := by
    have h := value.hSize
    rw [UScalar.size_UScalarTyU64, u64_size_eq] at h
    omega
  have hhigh :
      (Std.U64.wrapping_shr value 31#u32).val ≤ 8589934591 := by
    rw [u64_wrapping_shr31_val_eq, Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  have hand :
      (value &&& UScalar.cast .U64
        V5FriCoordinateAdapter.aspis_core.field.P).val ≤ 2147483647 := by
    calc
      _ ≤ (UScalar.cast .U64
          V5FriCoordinateAdapter.aspis_core.field.P).val :=
        u64_and_val_le_right _ _
      _ = 2147483647 := hmask
  have hfirstSum :
      (value &&& UScalar.cast .U64
          V5FriCoordinateAdapter.aspis_core.field.P).val +
        (Std.U64.wrapping_shr value 31#u32).val ≤ 10737418238 := by
    omega
  have hfirstSumLt :
      (value &&& UScalar.cast .U64
          V5FriCoordinateAdapter.aspis_core.field.P).val +
        (Std.U64.wrapping_shr value 31#u32).val < Std.U64.size := by
    rw [u64_size_eq]
    omega
  let first := Std.U64.wrapping_add
    (value &&& UScalar.cast .U64
      V5FriCoordinateAdapter.aspis_core.field.P)
    (Std.U64.wrapping_shr value 31#u32)
  have hfirst : first.val ≤ 10737418238 := by
    unfold first
    rw [Std.U64.wrapping_add_val_eq, UScalar.size_UScalarTyU64,
      Nat.mod_eq_of_lt hfirstSumLt]
    exact hfirstSum
  have hfirstHigh : (Std.U64.wrapping_shr first 31#u32).val ≤ 4 := by
    rw [u64_wrapping_shr31_val_eq, Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  have hfirstAnd :
      (first &&& UScalar.cast .U64
        V5FriCoordinateAdapter.aspis_core.field.P).val ≤ 2147483647 := by
    calc
      _ ≤ (UScalar.cast .U64
          V5FriCoordinateAdapter.aspis_core.field.P).val :=
        u64_and_val_le_right _ _
      _ = 2147483647 := hmask
  have hx1high :
      (Std.U64.wrapping_shr
        (Std.U64.wrapping_add
          (value &&& UScalar.cast .U64
            V5FriCoordinateAdapter.aspis_core.field.P)
          (Std.U64.wrapping_shr value 31#u32)) 31#u32).val ≤ 4 := by
    simpa [first] using hfirstHigh
  have hx1and :
      (Std.U64.wrapping_add
          (value &&& UScalar.cast .U64
            V5FriCoordinateAdapter.aspis_core.field.P)
          (Std.U64.wrapping_shr value 31#u32) &&&
        UScalar.cast .U64
          V5FriCoordinateAdapter.aspis_core.field.P).val ≤ 2147483647 := by
    simpa [first] using hfirstAnd
  simp only [Std.lift, bind_tc_ok]
  rw [checked_u64_shr31_eq_wrapping]
  simp only [bind_tc_ok]
  rw [checked_add_eq_wrapping]
  · simp only [bind_tc_ok]
    rw [generic_wrapping_add_eq_u64_wrapping_add]
    rw [checked_u64_shr31_eq_wrapping]
    simp only [bind_tc_ok]
    rw [checked_add_eq_wrapping]
    · simp only [bind_tc_ok]
      rw [generic_wrapping_add_eq_u64_wrapping_add]
      by_cases hreduce :
          UScalar.cast .U32
              (Std.U64.wrapping_add
                (Std.U64.wrapping_add
                    (value &&& UScalar.cast .U64
                      V5FriCoordinateAdapter.aspis_core.field.P)
                    (Std.U64.wrapping_shr value 31#u32) &&&
                  UScalar.cast .U64
                    V5FriCoordinateAdapter.aspis_core.field.P)
                (Std.U64.wrapping_shr
                  (Std.U64.wrapping_add
                    (value &&& UScalar.cast .U64
                      V5FriCoordinateAdapter.aspis_core.field.P)
                    (Std.U64.wrapping_shr value 31#u32)) 31#u32)) ≥
            V5FriCoordinateAdapter.aspis_core.field.P
      · simp [hreduce]
        rw [checked_sub_eq_wrapping]
        · rw [generic_wrapping_sub_eq_u32_wrapping_sub]
        · exact (UScalar.le_equiv _ _).1 hreduce
      · simp [hreduce]
    · rw [UScalar.max_UScalarTy_U64_eq, Std.U64.max_eq]
      omega
  · rw [UScalar.max_UScalarTy_U64_eq, Std.U64.max_eq]
    omega

/-- The production M31 multiplication is valid for every pair of raw U32
words, not only values already known canonical.  This is needed for the one
caller-supplied batch-inversion value; the reducer canonicalises the product. -/
theorem source_mul_arbitrary_corresponds (left right : M31) :
    ∃ output : M31,
      V5CoordinateSelectedProductionSource.field.M31.mul left right =
        .ok output ∧
      AspisV5FriCoordinateFieldSemantics.canonicalM31 output ∧
      m31Value output = m31Value left * m31Value right := by
  let left64 : Std.U64 := UScalar.cast .U64 left
  let right64 : Std.U64 := UScalar.cast .U64 right
  let product64 : Std.U64 := Std.U64.wrapping_mul left64 right64
  have hproductBound : left.val * right.val < 18446744073709551616 := by
    have hleft := left.hSize
    have hright := right.hSize
    rw [UScalar.size_UScalarTyU32] at hleft hright
    have hu32 : Std.U32.size = 4294967296 := u32_size_eq
    rw [hu32] at hleft hright
    nlinarith
  have hproductValue : product64.val = left.val * right.val := by
    unfold product64 left64 right64
    rw [Std.U64.wrapping_mul_val_eq, Std.U32.cast_U64_val_eq,
      Std.U32.cast_U64_val_eq, UScalar.size_UScalarTyU64, u64_size_eq,
      Nat.mod_eq_of_lt hproductBound]
  have hcheckedMul : (left64 * right64 : Result Std.U64) =
      .ok product64 := by
    apply checked_mul_eq_wrapping
    rw [Std.U32.cast_U64_val_eq, Std.U32.cast_U64_val_eq,
      UScalar.max_UScalarTy_U64_eq, Std.U64.max_eq]
    omega
  obtain ⟨output, hreduce, hcanonical, hvalue⟩ :=
    m31_reduce_u64_corresponds product64
  have hfreshReduce :
      V5FriArithmeticExact.field.reduce_u64 product64 = .ok output := by
    unfold V5FriArithmeticExact.field.M31.reduce_u64 at hreduce
    generalize hfield :
        V5FriArithmeticExact.field.reduce_u64 product64 = fieldResult
      at hreduce
    cases fieldResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hreduce
    | div => simp [Bind.bind, Aeneas.Std.bind] at hreduce
    | ok raw =>
        simp only [bind_tc_ok, Result.ok.injEq] at hreduce
        subst raw
        simpa using hfield
  have hsourceReduce :
      V5CoordinateSelectedProductionSource.field.reduce_u64 product64 =
        .ok output := by
    rw [source_reduce_u64_eq_adapter_arbitrary,
      adapter_reduce_eq_fresh_reduce]
    exact hfreshReduce
  refine ⟨output, ?_, hcanonical, ?_⟩
  · simp [V5CoordinateSelectedProductionSource.field.M31.mul,
      left64, right64, hcheckedMul, hsourceReduce, Std.lift]
  · rw [show m31Value output = (output.val : ZMod P) by rfl,
      hvalue, hproductValue]
    simp [m31Value]

theorem source_mul_arbitrary_call
    (left right output : M31)
    (hrun : V5CoordinateSelectedProductionSource.field.M31.mul left right =
      .ok output) :
    AspisV5FriCoordinateFieldSemantics.canonicalM31 output ∧
      m31Value output = m31Value left * m31Value right := by
  obtain ⟨exact, hexact, hcanonical, hvalue⟩ :=
    source_mul_arbitrary_corresponds left right
  rw [hrun] at hexact
  have heq := Result.ok.inj hexact
  subst exact
  exact ⟨hcanonical, hvalue⟩

theorem source_double_produces_canonical
    (input : M31)
    (hinput : AspisV5FriCoordinateFieldSemantics.canonicalM31 input) :
    ∃ output : M31,
      V5CoordinateSelectedProductionSource.field.M31.double input =
        .ok output ∧
      AspisV5FriCoordinateFieldSemantics.canonicalM31 output ∧
      m31Value output = 2 * m31Value input := by
  obtain ⟨output, hrun, hcanonical, hvalue⟩ :=
    AspisV5FriCoordinateFieldSemantics.double_produces_canonical input hinput
  refine ⟨output, ?_, hcanonical, hvalue⟩
  rw [source_double_eq_adapter_double input hinput]
  exact hrun

theorem source_is_zero_false (input : M31) (hnonzero : m31Value input ≠ 0) :
    V5CoordinateSelectedProductionSource.field.M31.is_zero input =
      .ok false := by
  have hraw : input ≠ 0#u32 := by
    intro heq
    apply hnonzero
    subst input
    rfl
  simp [V5CoordinateSelectedProductionSource.field.M31.is_zero, hraw]

theorem source_double_x_produces_canonical
    (input : M31)
    (hinput : AspisV5FriCoordinateFieldSemantics.canonicalM31 input) :
    ∃ output : M31,
      V5CoordinateSelectedProductionSource.circle_fri.double_x input =
        .ok output ∧
      AspisV5FriCoordinateFieldSemantics.canonicalM31 output ∧
      m31Value output = 2 * m31Value input ^ 2 - 1 := by
  obtain ⟨squared, hsquaredAdapter, hsquaredCanonical, hsquaredValue⟩ :=
    AspisV5FriCoordinateFieldSemantics.mul_produces_canonical input input
      hinput hinput
  have hsquared :
      V5CoordinateSelectedProductionSource.field.M31.mul input input =
        .ok squared := by
    rw [source_mul_eq_adapter_mul input input
      (canonical_m31_lt input hinput) (canonical_m31_lt input hinput)]
    exact hsquaredAdapter
  obtain ⟨doubled, hdoubledAdapter, hdoubledCanonical, hdoubledValue⟩ :=
    AspisV5FriCoordinateFieldSemantics.double_produces_canonical squared
      hsquaredCanonical
  have hdoubled :
      V5CoordinateSelectedProductionSource.field.M31.double squared =
        .ok doubled := by
    rw [source_double_eq_adapter_double squared hsquaredCanonical]
    exact hdoubledAdapter
  have honeCanonical :
      AspisV5FriCoordinateFieldSemantics.canonicalM31
        V5CoordinateSelectedProductionSource.field.M31.ONE := by
    norm_num [AspisV5FriCoordinateFieldSemantics.canonicalM31,
      AspisV5FriArithmeticSemantics.canonicalM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      V5CoordinateSelectedProductionSource.field.M31.ONE]
  obtain ⟨output, houtputArithmetic, houtputCanonical, houtputValue⟩ :=
    AspisV5FriArithmeticSemantics.m31_sub_corresponds doubled
      V5CoordinateSelectedProductionSource.field.M31.ONE
      hdoubledCanonical honeCanonical
  have houtput :
      V5CoordinateSelectedProductionSource.field.M31.sub doubled
          V5CoordinateSelectedProductionSource.field.M31.ONE =
        .ok output := by
    rw [source_sub_eq_adapter_sub doubled
      V5CoordinateSelectedProductionSource.field.M31.ONE
      (canonical_m31_lt doubled hdoubledCanonical)
      (canonical_m31_lt
        V5CoordinateSelectedProductionSource.field.M31.ONE honeCanonical),
      adapter_sub_eq_fresh_sub]
    exact houtputArithmetic
  refine ⟨output, ?_, houtputCanonical, ?_⟩
  · simp [V5CoordinateSelectedProductionSource.circle_fri.double_x,
      hsquared, hdoubled, houtput]
  · have houtputValue' : m31Value output = m31Value doubled - 1 := by
      simpa [m31Value,
        V5CoordinateSelectedProductionSource.field.M31.ONE] using
          houtputValue
    rw [houtputValue', hdoubledValue, hsquaredValue]
    ring

def sourceCoordinateTriple (first second third : M31) : Array M31 3#usize :=
  ⟨[first, second, third], by norm_num⟩

def sourceKindTriple : Array
    V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator 3#usize :=
  ⟨[
    V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator.LineFirstPairX,
    V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator.LineSecondPairX,
    V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator.LineSecondFoldX],
    by norm_num⟩

def sourceThreeZipAt (first second third : M31) (index : Nat) :
    core.iter.adapters.zip.Zip (V5CoordinateSelectedProductionSource.core.array.iter.IntoIter M31 3#usize)
      (V5CoordinateSelectedProductionSource.core.array.iter.IntoIter
        V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator
        3#usize) :=
  ⟨⟨sourceCoordinateTriple first second third, index⟩,
    ⟨sourceKindTriple, index⟩⟩

def sourceThreeZip (first second third : M31) :=
  sourceThreeZipAt first second third 0

private theorem source_three_zip_next_zero (first second third : M31) :
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
        (V5CoordinateSelectedProductionSource.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator M31 3#usize)
        (V5CoordinateSelectedProductionSource.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator 3#usize)
        (sourceThreeZipAt first second third 0) =
      .ok (some (first,
        V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator.LineFirstPairX),
        sourceThreeZipAt first second third 1) := by
  rfl

private theorem source_three_zip_next_one (first second third : M31) :
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
        (V5CoordinateSelectedProductionSource.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator M31 3#usize)
        (V5CoordinateSelectedProductionSource.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator 3#usize)
        (sourceThreeZipAt first second third 1) =
      .ok (some (second,
        V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator.LineSecondPairX),
        sourceThreeZipAt first second third 2) := by
  rfl

private theorem source_three_zip_next_two (first second third : M31) :
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
        (V5CoordinateSelectedProductionSource.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator M31 3#usize)
        (V5CoordinateSelectedProductionSource.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator 3#usize)
        (sourceThreeZipAt first second third 2) =
      .ok (some (third,
        V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator.LineSecondFoldX),
        sourceThreeZipAt first second third 3) := by
  rfl

private theorem source_three_zip_next_three (first second third : M31) :
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
        (V5CoordinateSelectedProductionSource.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator M31 3#usize)
        (V5CoordinateSelectedProductionSource.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator 3#usize)
        (sourceThreeZipAt first second third 3) =
      .ok (none, sourceThreeZipAt first second third 3) := by
  rfl

def sourceAppendThree (first second third : M31) (values : M31Vec) :
    Result (M31Vec × Option (core.result.Result Output
      V5CoordinateSelectedProductionSource.circle_fri.CircleFriError)) :=
  V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3_loop0
    (sourceThreeZip first second third) values

private theorem source_append_three_exact
    (first second third : M31) (values : M31Vec)
    (hfirst : m31Value first ≠ 0)
    (hsecond : m31Value second ≠ 0)
    (hthird : m31Value third ≠ 0)
    (hcapacity : values.val.length + 3 ≤ Std.Usize.max) :
    ∃ output : M31Vec,
      sourceAppendThree first second third values = .ok (output, none) ∧
      output.val = values.val ++ [first, second, third] := by
  have hz0 := source_is_zero_false first hfirst
  have hz1 := source_is_zero_false second hsecond
  have hz2 := source_is_zero_false third hthird
  obtain ⟨v1, hv1, hval1⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec values first (by omega))
  obtain ⟨v2, hv2, hval2⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec v1 second (by
      rw [hval1, List.length_append]
      simp only [List.length_singleton]
      omega))
  obtain ⟨v3, hv3, hval3⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.push_spec v2 third (by
      rw [hval2, hval1, List.length_append, List.length_append]
      simp only [List.length_singleton]
      omega))
  refine ⟨v3, ?_, ?_⟩
  · unfold sourceAppendThree
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3_loop0
    rw [loop.eq_def]
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3_loop0.body
    simp only
    rw [show sourceThreeZip first second third =
      sourceThreeZipAt first second third 0 by rfl,
      source_three_zip_next_zero]
    simp only [bind_tc_ok]
    rw [hz0]
    simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte]
    rw [hv1]
    simp only [bind_tc_ok]
    rw [loop.eq_def]
    simp only
    rw [source_three_zip_next_one]
    simp only [bind_tc_ok]
    rw [hz1]
    simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte]
    rw [hv2]
    simp only [bind_tc_ok]
    rw [loop.eq_def]
    simp only
    rw [source_three_zip_next_two]
    simp only [bind_tc_ok]
    rw [hz2]
    simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte]
    rw [hv3]
    simp only [bind_tc_ok]
    rw [loop.eq_def]
    simp only
    rw [source_three_zip_next_three]
    simp only [bind_tc_ok]
  · rw [hval3, hval2, hval1]
    simp

def SourceCanonicalM31Vec (values : M31Vec) : Prop :=
  ∀ value, value ∈ values.val →
    AspisV5FriCoordinateFieldSemantics.canonicalM31 value

def SourceCanonicalPoints (points : PointVec) : Prop :=
  ∀ index, index < points.val.length →
    pointCanonical (toAdapterPoint points.val[index]!)

def sourcePointIter (points : PointVec) (index : Nat) :
    core.slice.iter.Iter Point :=
  { slice := ⟨points.val, points.property⟩, i := index }

private theorem source_point_iter_next_some
    (points : PointVec) (index : Nat) (hindex : index < points.val.length) :
    core.slice.iter.IteratorSliceIter.next (sourcePointIter points index) =
      .ok (some points.val[index]!, sourcePointIter points (index + 1)) := by
  unfold core.slice.iter.IteratorSliceIter.next sourcePointIter
  rw [dif_pos (by simpa [Slice.len_val] using hindex)]
  rw [getElemBang_eq_getElem points.val index hindex]
  rfl

private theorem source_point_iter_next_none
    (points : PointVec) (index : Nat) (hindex : points.val.length ≤ index) :
    core.slice.iter.IteratorSliceIter.next (sourcePointIter points index) =
      .ok (none, sourcePointIter points index) := by
  unfold core.slice.iter.IteratorSliceIter.next sourcePointIter
  rw [dif_neg (by simpa [Slice.len_val] using hindex)]

private def SourceLinePointInvariant
    (initial : M31Vec) (points : PointVec)
    (state : core.slice.iter.Iter Point × M31Vec) : Prop :=
  state.1 = sourcePointIter points state.1.i ∧
  state.1.i ≤ points.val.length ∧
  state.2.val.length = initial.val.length + 3 * state.1.i ∧
  SourceCanonicalM31Vec state.2 ∧
  (∀ index, index < initial.val.length →
    state.2.val[index]! = initial.val[index]!) ∧
  ∀ index, index < state.1.i →
    m31Value state.2.val[initial.val.length + 3 * index]! =
        2 * m31Value points.val[index]!.x ∧
    m31Value state.2.val[initial.val.length + 3 * index + 1]! =
        2 * m31Value points.val[index]!.y ∧
    m31Value state.2.val[initial.val.length + 3 * index + 2]! =
        2 * (2 * m31Value points.val[index]!.x ^ 2 - 1)

def SourceLinePointPost
    (initial : M31Vec) (points : PointVec)
    (out : M31Vec × Option (core.result.Result Output
      V5CoordinateSelectedProductionSource.circle_fri.CircleFriError)) : Prop :=
  out.1.val.length = initial.val.length + 3 * points.val.length ∧
  SourceCanonicalM31Vec out.1 ∧
  out.2 = none ∧
  (∀ index, index < initial.val.length →
    out.1.val[index]! = initial.val[index]!) ∧
  ∀ index, index < points.val.length →
    m31Value out.1.val[initial.val.length + 3 * index]! =
        2 * m31Value points.val[index]!.x ∧
    m31Value out.1.val[initial.val.length + 3 * index + 1]! =
        2 * m31Value points.val[index]!.y ∧
    m31Value out.1.val[initial.val.length + 3 * index + 2]! =
        2 * (2 * m31Value points.val[index]!.x ^ 2 - 1)

/-- The unchanged extracted line-point iterator appends exactly the three
released denominators for every point, in source order. -/
theorem source_line_point_denominator_loop_exact
    (initial : M31Vec) (points : PointVec)
    (hinitial : SourceCanonicalM31Vec initial)
    (hpoints : SourceCanonicalPoints points)
    (hcapacity : initial.val.length + 3 * points.val.length ≤
      Std.Usize.max)
    (hnonzero : ∀ index, index < points.val.length →
      2 * m31Value points.val[index]!.x ≠ 0 ∧
      2 * m31Value points.val[index]!.y ≠ 0 ∧
      2 * (2 * m31Value points.val[index]!.x ^ 2 - 1) ≠ 0) :
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3
        (sourcePointIter points 0) initial
      ⦃ out => SourceLinePointPost initial points out ⦄ := by
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3
  apply loop.spec_decr_nat
    (fun state => points.val.length - state.1.i)
    (SourceLinePointInvariant initial points)
    (SourceLinePointPost initial points)
  · rintro ⟨iter, current⟩ hstate
    rcases hstate with
      ⟨hiter, hordinalLe, hlength, hcanonical, hprefix, hvalues⟩
    simp only at hiter hordinalLe hlength hcanonical hprefix hvalues
    rw [hiter]
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3.body
    let ordinal := iter.i
    by_cases hactive : ordinal < points.val.length
    · have hpointCanonical :
          pointCanonical (toAdapterPoint points.val[ordinal]!) :=
        hpoints ordinal hactive
      obtain ⟨first, hfirstRun, hfirstCanonical, hfirstValue⟩ :=
        source_double_produces_canonical points.val[ordinal]!.x
          hpointCanonical.1
      obtain ⟨second, hsecondRun, hsecondCanonical, hsecondValue⟩ :=
        source_double_produces_canonical points.val[ordinal]!.y
          hpointCanonical.2
      obtain ⟨foldX, hfoldXRun, hfoldXCanonical, hfoldXValue⟩ :=
        source_double_x_produces_canonical points.val[ordinal]!.x
          hpointCanonical.1
      obtain ⟨third, hthirdRun, hthirdCanonical, hthirdValue⟩ :=
        source_double_produces_canonical foldX hfoldXCanonical
      have hpointNonzero := hnonzero ordinal hactive
      have hfirstNonzero : m31Value first ≠ 0 := by
        rw [hfirstValue]
        exact hpointNonzero.1
      have hsecondNonzero : m31Value second ≠ 0 := by
        rw [hsecondValue]
        exact hpointNonzero.2.1
      have hthirdNonzero : m31Value third ≠ 0 := by
        rw [hthirdValue, hfoldXValue]
        exact hpointNonzero.2.2
      have hinnerCapacity : current.val.length + 3 ≤ Std.Usize.max := by
        rw [hlength]
        omega
      obtain ⟨next, hinnerRun, hnextValue⟩ :=
        source_append_three_exact first second third current
          hfirstNonzero hsecondNonzero hthirdNonzero hinnerCapacity
      have hinnerRun' :
          V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3_loop0
              (sourceThreeZip first second third) current =
            .ok (next, none) := by
        simpa [sourceAppendThree] using hinnerRun
      have hbodyZip :
          (⟨
            ⟨Array.make 3#usize [first, second, third], 0⟩,
            ⟨Array.make 3#usize [
              V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator.LineFirstPairX,
              V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator.LineSecondPairX,
              V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator.LineSecondFoldX], 0⟩
          ⟩ : core.iter.adapters.zip.Zip
            (V5CoordinateSelectedProductionSource.core.array.iter.IntoIter M31 3#usize)
            (V5CoordinateSelectedProductionSource.core.array.iter.IntoIter
              V5CoordinateSelectedProductionSource.circle_fri.FoldDenominator
              3#usize)) = sourceThreeZip first second third := by
        rfl
      simp only
      rw [source_point_iter_next_some points ordinal hactive]
      simp only [bind_tc_ok]
      rw [hfirstRun]
      simp only [bind_tc_ok]
      rw [hsecondRun]
      simp only [bind_tc_ok]
      rw [hfoldXRun]
      simp only [bind_tc_ok]
      rw [hthirdRun]
      simp only [bind_tc_ok]
      simp only [
        V5CoordinateSelectedProductionSource.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
        core.iter.traits.iterator.Iterator.zip.trait_default,
        core.iter.traits.iterator.Iterator.zip.default, bind_tc_ok]
      rw [hbodyZip]
      rw [hinnerRun']
      simp only [bind_tc_ok, WP.spec_ok]
      change SourceLinePointInvariant initial points
          (sourcePointIter points (ordinal + 1), next) ∧
        points.val.length - (ordinal + 1) <
          points.val.length - ordinal
      refine ⟨?_, by omega⟩
      unfold SourceLinePointInvariant
      simp only [sourcePointIter]
      have hnextLength :
          next.val.length = initial.val.length + 3 * (ordinal + 1) := by
        rw [hnextValue, List.length_append, hlength]
        simp
        omega
      have hnextCanonical : SourceCanonicalM31Vec next := by
        intro value hvalue
        rw [hnextValue] at hvalue
        rcases List.mem_append.mp hvalue with hvalue | hvalue
        · exact hcanonical value hvalue
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hvalue
          rcases hvalue with rfl | rfl | rfl
          · exact hfirstCanonical
          · exact hsecondCanonical
          · exact hthirdCanonical
      have hnextPrefix : ∀ index, index < initial.val.length →
          next.val[index]! = initial.val[index]! := by
        intro index hindex
        have hcurrentBound : index < current.val.length := by omega
        have hnextBang := congrArg (fun values => values[index]!) hnextValue
        rw [hnextBang, getElemBang_append_left _ _ _ hcurrentBound]
        exact hprefix index hindex
      refine ⟨True.intro, by omega, hnextLength, hnextCanonical,
        hnextPrefix, ?_⟩
      intro index hindex
      by_cases hold : index < ordinal
      · have holdValues := hvalues index hold
        have hslot0 : initial.val.length + 3 * index < current.val.length := by
          omega
        have hslot1 : initial.val.length + 3 * index + 1 < current.val.length := by
          omega
        have hslot2 : initial.val.length + 3 * index + 2 < current.val.length := by
          omega
        have hsame (slot : Nat) (hslot : slot < current.val.length) :
            next.val[slot]! = current.val[slot]! := by
          have hnextBang := congrArg (fun values => values[slot]!) hnextValue
          rw [hnextBang]
          exact getElemBang_append_left _ _ _ hslot
        rw [hsame _ hslot0, hsame _ hslot1, hsame _ hslot2]
        exact holdValues
      · have hnew : index = ordinal := by omega
        subst index
        have hslot : initial.val.length + 3 * ordinal =
            current.val.length := by omega
        have hfirstAt : next.val[current.val.length]! = first := by
          have hnextBang := congrArg
            (fun values => values[current.val.length]!) hnextValue
          rw [hnextBang]
          simp
        have hsecondAt : next.val[current.val.length + 1]! = second := by
          have hnextBang := congrArg
            (fun values => values[current.val.length + 1]!) hnextValue
          rw [hnextBang]
          simp
        have hthirdAt : next.val[current.val.length + 2]! = third := by
          have hnextBang := congrArg
            (fun values => values[current.val.length + 2]!) hnextValue
          rw [hnextBang]
          simp
        rw [hslot, hfirstAt, hsecondAt, hthirdAt,
          hfirstValue, hsecondValue, hthirdValue, hfoldXValue]
        exact ⟨rfl, rfl, rfl⟩
    · have hdone : ordinal = points.val.length := by omega
      simp only
      rw [source_point_iter_next_none points ordinal (by omega)]
      simp only [bind_tc_ok, WP.spec_ok]
      unfold SourceLinePointPost
      simp only
      change iter.i = points.val.length at hdone
      rw [hdone] at hlength hvalues
      exact ⟨hlength, hcanonical, True.intro, hprefix, hvalues⟩
  · unfold SourceLinePointInvariant SourceCanonicalM31Vec sourcePointIter
    simp only
    refine ⟨True.intro, by simp, ?_, hinitial,
      (fun _ hindex => by simpa using hindex), ?_⟩
    · norm_num
    · intro index hindex
      norm_num at hindex

def sourcePointVecTriple (line1 line2 line3 : PointVec) :
    Array PointVec 3#usize :=
  ⟨[line1, line2, line3], by norm_num⟩

def sourcePointVecIterAt (line1 line2 line3 : PointVec) (index : Nat) :
    V5CoordinateSelectedProductionSource.core.array.iter.IntoIter PointVec 3#usize :=
  ⟨sourcePointVecTriple line1 line2 line3, index⟩

private theorem source_point_vec_next_zero
    (line1 line2 line3 : PointVec) :
    V5CoordinateSelectedProductionSource.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
        (sourcePointVecIterAt line1 line2 line3 0) =
      .ok (some line1, sourcePointVecIterAt line1 line2 line3 1) := by
  rfl

private theorem source_point_vec_next_one
    (line1 line2 line3 : PointVec) :
    V5CoordinateSelectedProductionSource.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
        (sourcePointVecIterAt line1 line2 line3 1) =
      .ok (some line2, sourcePointVecIterAt line1 line2 line3 2) := by
  rfl

private theorem source_point_vec_next_two
    (line1 line2 line3 : PointVec) :
    V5CoordinateSelectedProductionSource.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
        (sourcePointVecIterAt line1 line2 line3 2) =
      .ok (some line3, sourcePointVecIterAt line1 line2 line3 3) := by
  rfl

private theorem source_point_vec_next_three
    (line1 line2 line3 : PointVec) :
    V5CoordinateSelectedProductionSource.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
        (sourcePointVecIterAt line1 line2 line3 3) =
      .ok (none, sourcePointVecIterAt line1 line2 line3 3) := by
  rfl

/-- The unchanged fixed outer iterator invokes the three later-layer point
loops in order.  Its terminal batch/output branch is an explicit premise for
this composition lemma and is discharged separately below. -/
theorem source_three_line_outer_unroll
    (layer0 : Slice Std.U32) (later : Array (Slice Std.U32) 3#usize)
    (inverse : M31 → M31)
    (line1 line2 line3 : PointVec)
    (denominatorCount : Std.Usize)
    (initial after1 after2 after3 : M31Vec)
    (result : core.result.Result Output
      V5CoordinateSelectedProductionSource.circle_fri.CircleFriError)
    (hline1 :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3
          (sourcePointIter line1 0) initial = .ok (after1, none))
    (hline2 :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3
          (sourcePointIter line2 0) after1 = .ok (after2, none))
    (hline3 :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3
          (sourcePointIter line3 0) after2 = .ok (after3, none))
    (hterminal :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
          (sourcePointVecIterAt line1 line2 line3 3) layer0 later inverse
          line3 denominatorCount after3 = .ok result) :
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
        (sourcePointVecIterAt line1 line2 line3 0) layer0 later inverse
        line3 denominatorCount initial = .ok result := by
  simp only [sourcePointIter] at hline1 hline2 hline3
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
  rw [loop.eq_def]
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0.body
  simp only
  rw [source_point_vec_next_zero]
  simp only [bind_tc_ok,
    V5CoordinateSelectedProductionSource.SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter]
  rw [hline1]
  simp only [bind_tc_ok]
  rw [loop.eq_def]
  simp only
  rw [source_point_vec_next_one]
  simp only [bind_tc_ok,
    V5CoordinateSelectedProductionSource.SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter]
  rw [hline2]
  simp only [bind_tc_ok]
  rw [loop.eq_def]
  simp only
  rw [source_point_vec_next_two]
  simp only [bind_tc_ok,
    V5CoordinateSelectedProductionSource.SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter]
  rw [hline3]
  simp only [bind_tc_ok]
  change
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
        (sourcePointVecIterAt line1 line2 line3 3) layer0 later inverse
        line3 denominatorCount after3 = .ok result
  exact hterminal

/-- Acceptance of the three fixed later-line iterations transports to the
terminal batch/output call with the same successful result. -/
theorem source_three_line_outer_accepted
    (layer0 : Slice Std.U32) (later : Array (Slice Std.U32) 3#usize)
    (inverse : M31 → M31)
    (line1 line2 line3 : PointVec)
    (denominatorCount : Std.Usize)
    (initial after1 after2 after3 : M31Vec)
    (result : core.result.Result Output
      V5CoordinateSelectedProductionSource.circle_fri.CircleFriError)
    (hline1 :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3
          (sourcePointIter line1 0) initial = .ok (after1, none))
    (hline2 :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3
          (sourcePointIter line2 0) after1 = .ok (after2, none))
    (hline3 :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop3
          (sourcePointIter line3 0) after2 = .ok (after3, none))
    (haccepted :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
        (sourcePointVecIterAt line1 line2 line3 0) layer0 later inverse
        line3 denominatorCount initial = .ok result) :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
        (sourcePointVecIterAt line1 line2 line3 3) layer0 later inverse
        line3 denominatorCount after3 = .ok result := by
  simp only [sourcePointIter] at hline1 hline2 hline3
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
    at haccepted
  rw [loop.eq_def] at haccepted
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0.body
    at haccepted
  simp only at haccepted
  rw [source_point_vec_next_zero] at haccepted
  simp only [bind_tc_ok,
    V5CoordinateSelectedProductionSource.SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter]
    at haccepted
  rw [hline1] at haccepted
  simp only [bind_tc_ok] at haccepted
  rw [loop.eq_def] at haccepted
  simp only at haccepted
  rw [source_point_vec_next_one] at haccepted
  simp only [bind_tc_ok,
    V5CoordinateSelectedProductionSource.SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter]
    at haccepted
  rw [hline2] at haccepted
  simp only [bind_tc_ok] at haccepted
  rw [loop.eq_def] at haccepted
  simp only at haccepted
  rw [source_point_vec_next_two] at haccepted
  simp only [bind_tc_ok,
    V5CoordinateSelectedProductionSource.SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter]
    at haccepted
  rw [hline3] at haccepted
  simp only [bind_tc_ok] at haccepted
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
  exact haccepted

def SourceCanonicalSlice (values : Slice M31) : Prop :=
  ∀ index, index < values.val.length →
    AspisV5FriCoordinateFieldSemantics.canonicalM31 values.val[index]!

private theorem sourceCanonicalSlice_set
    (values : Slice M31) (index : Std.Usize) (value : M31)
    (hvalues : SourceCanonicalSlice values)
    (hindex : index.val < values.val.length)
    (hvalue : AspisV5FriCoordinateFieldSemantics.canonicalM31 value) :
    SourceCanonicalSlice (values.set index value) := by
  intro slot hslot
  have hlength : (values.val.set index.val value).length =
      values.val.length := List.length_set
  change slot < (values.val.set index.val value).length at hslot
  change AspisV5FriCoordinateFieldSemantics.canonicalM31
    (values.val.set index.val value)[slot]!
  have hold : slot < values.val.length := by simpa [hlength] using hslot
  rw [getElemBang_eq_getElem _ _ hslot,
    List.getElem_set]
  by_cases heq : index.val = slot
  · simp [heq, hvalue]
  · simp [heq]
    have hcanonical := hvalues slot hold
    rwa [getElemBang_eq_getElem values.val slot hold] at hcanonical

private theorem source_prefixProduct_succ
    (denominators : M31Vec) (index : Nat)
    (hindex : index < denominators.val.length) :
    prefixProduct denominators (index + 1) =
      prefixProduct denominators index *
        m31Value denominators.val[index]! := by
  unfold prefixProduct
  have htake := List.take_concat_get' denominators.val index hindex
  change
    ((denominators.val.take (index + 1)).map m31Value).prod =
      ((denominators.val.take index).map m31Value).prod *
        m31Value denominators.val[index]!
  rw [← htake, List.map_append, List.prod_append]
  simp [List.getElem!_eq_getElem?_getD, hindex]

private def sourceM31Iter (values : M31Vec) (index : Nat) :
    core.slice.iter.Iter M31 :=
  { slice := ⟨values.val, values.property⟩, i := index }

private theorem source_m31_iter_next_some
    (values : M31Vec) (index : Nat) (hindex : index < values.val.length) :
    core.slice.iter.IteratorSliceIter.next (sourceM31Iter values index) =
      .ok (some values.val[index]!, sourceM31Iter values (index + 1)) := by
  unfold core.slice.iter.IteratorSliceIter.next sourceM31Iter
  rw [dif_pos (by simpa [Slice.len_val] using hindex)]
  rw [getElemBang_eq_getElem values.val index hindex]
  rfl

private theorem source_m31_iter_next_none
    (values : M31Vec) (index : Nat) (hindex : values.val.length ≤ index) :
    core.slice.iter.IteratorSliceIter.next (sourceM31Iter values index) =
      .ok (none, sourceM31Iter values index) := by
  unfold core.slice.iter.IteratorSliceIter.next sourceM31Iter
  rw [dif_neg (by simpa [Slice.len_val] using hindex)]

private def SourcePrefixInvariant
    (denominators : M31Vec)
    (state : core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter M31) × Slice M31 × M31) : Prop :=
  state.1.iter.slice.val = denominators.val ∧
  state.1.iter.i = state.1.count.val ∧
  state.1.count.val ≤ denominators.val.length ∧
  state.2.1.val.length = denominators.val.length ∧
  SourceCanonicalSlice state.2.1 ∧
  AspisV5FriCoordinateFieldSemantics.canonicalM31 state.2.2 ∧
  m31Value state.2.2 = prefixProduct denominators state.1.count.val ∧
  ∀ index, index < state.1.count.val →
    m31Value state.2.1.val[index]! = prefixProduct denominators index

def SourcePrefixPost
    (denominators : M31Vec) (out : Slice M31 × M31) : Prop :=
  out.1.val.length = denominators.val.length ∧
  SourceCanonicalSlice out.1 ∧
  AspisV5FriCoordinateFieldSemantics.canonicalM31 out.2 ∧
  m31Value out.2 = prefixProduct denominators denominators.val.length ∧
  ∀ index, index < denominators.val.length →
    m31Value out.1.val[index]! = prefixProduct denominators index

/-- The unchanged production forward batch-inverse pass stores the exact
prefix product before every denominator and returns the full product. -/
theorem source_prefix_loop_exact
    (denominators : M31Vec)
    (enumerated : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter M31))
    (out : Slice M31) (accumulator : M31)
    (hinvariant : SourcePrefixInvariant denominators
      (enumerated, out, accumulator)) :
    V5CoordinateSelectedProductionSource.field.m31_batch_inverse_with_loop0
        enumerated out accumulator
      ⦃ result => SourcePrefixPost denominators result ⦄ := by
  unfold V5CoordinateSelectedProductionSource.field.m31_batch_inverse_with_loop0
  apply loop.spec_decr_nat
    (fun state => denominators.val.length - state.1.count.val)
    (SourcePrefixInvariant denominators)
    (SourcePrefixPost denominators)
  · rintro ⟨currentIter, currentOut, currentAccumulator⟩ hstate
    rcases hstate with
      ⟨hslice, hinnerIndex, hindexLe, hlength, hcanonical,
        haccCanonical, haccValue, hprefix⟩
    simp only at hslice hinnerIndex hindexLe hlength hcanonical haccCanonical haccValue hprefix
    unfold
      V5CoordinateSelectedProductionSource.field.m31_batch_inverse_with_loop0.body
    simp only
    have hiterEq : currentIter.iter =
        sourceM31Iter denominators currentIter.count.val := by
      cases hcurrent : currentIter.iter with
      | mk currentSlice currentIndex =>
          have hslice' : currentSlice.val = denominators.val := by
            simpa [hcurrent] using hslice
          have hinnerIndex' : currentIndex = currentIter.count.val := by
            simpa [hcurrent] using hinnerIndex
          unfold sourceM31Iter
          rw [hinnerIndex']
          have hsliceEq : currentSlice =
              ⟨denominators.val, denominators.property⟩ :=
            Subtype.ext hslice'
          subst currentSlice
          rfl
    by_cases hactive : currentIter.count.val < denominators.val.length
    · let value := denominators.val[currentIter.count.val]!
      let innerNext : core.slice.iter.Iter M31 :=
        sourceM31Iter denominators (currentIter.count.val + 1)
      have hinnerRun :
          core.slice.iter.IteratorSliceIter.next currentIter.iter =
            .ok (some value, innerNext) := by
        rw [hiterEq]
        exact source_m31_iter_next_some denominators currentIter.count.val
          hactive
      have hinnerSpec :
          (core.iter.traits.iterator.IteratorSliceIter M31).next
              currentIter.iter
            ⦃ pair => pair.1 = some value ∧ pair.2 = innerNext ⦄ := by
        change core.slice.iter.IteratorSliceIter.next currentIter.iter
            ⦃ pair => pair.1 = some value ∧ pair.2 = innerNext ⦄
        rw [hinnerRun]
        simp only [WP.spec_ok, and_self]
      have hcountRoom : currentIter.count.val + 1 ≤ Std.Usize.max := by
        have hdenomMax := denominators.property
        omega
      obtain ⟨⟨nextOption, nextIter⟩, hnextRun,
          hnextOption, hnextInner, hnextCount⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
            (core.iter.traits.iterator.IteratorSliceIter M31)
            currentIter value innerNext hinnerSpec hcountRoom)
      have houtputBound : currentIter.count.val < currentOut.val.length := by
        rwa [hlength]
      obtain ⟨nextOut, hupdateRun, hnextOutEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (Slice.update_spec currentOut currentIter.count
            currentAccumulator houtputBound)
      obtain ⟨nextAccumulator, hmulRun, hnextAccCanonical,
          hnextAccValue⟩ :=
        source_mul_arbitrary_corresponds currentAccumulator value
      rw [hnextRun]
      simp only [bind_tc_ok]
      rw [hnextOption]
      simp only
      rw [hupdateRun]
      simp only [bind_tc_ok]
      rw [hmulRun]
      simp only [bind_tc_ok, WP.spec_ok]
      change SourcePrefixInvariant denominators
          (nextIter, nextOut, nextAccumulator) ∧
        denominators.val.length - nextIter.count.val <
          denominators.val.length - currentIter.count.val
      have hnextSlice : nextIter.iter.slice.val = denominators.val := by
        rw [hnextInner]
        rfl
      have hnextIndex : nextIter.iter.i = nextIter.count.val := by
        rw [hnextInner, hnextCount]
        rfl
      have hnextLength : nextOut.val.length = denominators.val.length := by
        rw [hnextOutEq]
        simp [hlength]
      have hnextCanonical : SourceCanonicalSlice nextOut := by
        rw [hnextOutEq]
        exact sourceCanonicalSlice_set currentOut currentIter.count
          currentAccumulator hcanonical houtputBound haccCanonical
      refine ⟨?_, by rw [hnextCount]; omega⟩
      unfold SourcePrefixInvariant
      simp only
      refine ⟨hnextSlice, hnextIndex, by rw [hnextCount]; omega,
        hnextLength, hnextCanonical, hnextAccCanonical, ?_, ?_⟩
      · rw [hnextCount,
          source_prefixProduct_succ denominators currentIter.count.val
            hactive, ← haccValue]
        exact hnextAccValue
      · intro slot hslot
        by_cases heq : slot = currentIter.count.val
        · subst slot
          rw [hnextOutEq]
          let setValues :=
            currentOut.val.set currentIter.count.val currentAccumulator
          change m31Value setValues[currentIter.count.val]! =
              prefixProduct denominators currentIter.count.val
          have hsetBound : currentIter.count.val <
              (currentOut.val.set currentIter.count.val currentAccumulator).length := by
            simpa using houtputBound
          rw [getElemBang_eq_getElem _ _ hsetBound, List.getElem_set]
          simp [haccValue]
        · have hslotOld : slot < currentIter.count.val := by
            rw [hnextCount] at hslot
            omega
          have hslotBound : slot < currentOut.val.length := by omega
          rw [hnextOutEq]
          let setValues :=
            currentOut.val.set currentIter.count.val currentAccumulator
          change m31Value setValues[slot]! = prefixProduct denominators slot
          have hsetBound : slot <
              setValues.length := by
            simpa only [setValues, List.length_set] using hslotBound
          rw [getElemBang_eq_getElem _ _ hsetBound, List.getElem_set]
          have hne : currentIter.count.val ≠ slot := by
            intro hsame
            exact heq hsame.symm
          simp [hne]
          have hold := hprefix slot hslotOld
          rw [getElemBang_eq_getElem _ _ hslotBound] at hold
          exact hold
    · have hdone : currentIter.count.val = denominators.val.length := by
        omega
      have hinnerRun :
          core.slice.iter.IteratorSliceIter.next currentIter.iter =
            .ok (none, currentIter.iter) := by
        rw [hiterEq]
        simpa using source_m31_iter_next_none denominators
          currentIter.count.val (by omega)
      have hinnerSpec :
          (core.iter.traits.iterator.IteratorSliceIter M31).next
              currentIter.iter
            ⦃ pair => pair.1 = none ∧ pair.2 = currentIter.iter ⦄ := by
        change core.slice.iter.IteratorSliceIter.next currentIter.iter
            ⦃ pair => pair.1 = none ∧ pair.2 = currentIter.iter ⦄
        rw [hinnerRun]
        simp only [WP.spec_ok, and_self]
      obtain ⟨⟨nextOption, nextIter⟩, hnextRun,
          hnextOption, _hnextInner, _hnextCount⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (core.iter.adapters.enumerate.IteratorEnumerate.next_none_spec
            (core.iter.traits.iterator.IteratorSliceIter M31)
            currentIter currentIter.iter hinnerSpec)
      rw [hnextRun]
      simp only [bind_tc_ok]
      rw [hnextOption]
      simp only [WP.spec_ok]
      rw [hdone] at haccValue hprefix
      exact ⟨hlength, hcanonical, haccCanonical, haccValue, hprefix⟩
  · exact hinvariant

private def sourcePrevious (suffix : Std.Usize) (hactive : 0 < suffix.val) :
    Std.Usize :=
  Std.Usize.ofNatCore (suffix.val - 1) (by scalar_tac)

private def sourceRevRange (suffix : Std.Usize) :
    core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize) :=
  ⟨{ start := 0#usize, «end» := suffix }⟩

private theorem sourcePrevious_val
    (suffix : Std.Usize) (hactive : 0 < suffix.val) :
    (sourcePrevious suffix hactive).val = suffix.val - 1 := by
  rfl

private theorem source_rev_range_next_some
    (suffix : Std.Usize) (hactive : 0 < suffix.val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize)
        (sourceRevRange suffix) =
      .ok (some (sourcePrevious suffix hactive),
        sourceRevRange (sourcePrevious suffix hactive)) := by
  unfold
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
    core.ops.range.Range.Insts.DoubleEndedIterator
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back
    core.iter.range.StepUsize core.iter.range.UScalarStep
    core.iter.range.UScalarStep.backward_checked
    sourceRevRange sourcePrevious
  simp only [core.cmp.impls.PartialOrdUsize.lt, bind_tc_ok]
  rw [dif_pos (by norm_num; omega)]
  simp only [bind_tc_ok]
  simp [hactive]
  apply UScalar.eq_of_val_eq
  rfl

private theorem source_rev_range_next_none :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize)
        (sourceRevRange 0#usize) =
      .ok (none, sourceRevRange 0#usize) := by
  unfold
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
    core.ops.range.Range.Insts.DoubleEndedIterator
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back
    core.iter.range.StepUsize core.iter.range.UScalarStep
    sourceRevRange
  simp [core.cmp.impls.PartialOrdUsize.lt]

private theorem source_suffixProduct_at
    (denominators : M31Vec) (index : Nat)
    (hindex : index < denominators.val.length) :
    suffixProduct denominators index =
      m31Value denominators.val[index]! *
        suffixProduct denominators (index + 1) := by
  unfold suffixProduct
  change
    ((denominators.val.drop index).map m31Value).prod =
      m31Value denominators.val[index]! *
        ((denominators.val.drop (index + 1)).map m31Value).prod
  have hmappedIndex :
      index < (denominators.val.map m31Value).length := by
    simpa using hindex
  simp only [List.map_drop]
  rw [List.drop_eq_getElem_cons hmappedIndex]
  simp [getElemBang_eq_getElem denominators.val index hindex]

private def SourceSuffixInvariant
    (denominators : M31Vec) (backend : ZMod P)
    (state : core.iter.adapters.rev.Rev
        (core.ops.range.Range Std.Usize) × Slice M31 × M31) : Prop :=
  state.1 = sourceRevRange state.1.iter.«end» ∧
  state.1.iter.«end».val ≤ denominators.val.length ∧
  state.2.1.val.length = denominators.val.length ∧
  SourceCanonicalSlice state.2.1 ∧
  m31Value state.2.2 =
    backend * suffixProduct denominators state.1.iter.«end».val ∧
  (∀ index, index < state.1.iter.«end».val →
    m31Value state.2.1.val[index]! = prefixProduct denominators index) ∧
  ∀ index, state.1.iter.«end».val ≤ index →
      index < denominators.val.length →
    m31Value state.2.1.val[index]! =
      prefixProduct denominators index * backend *
        suffixProduct denominators (index + 1)

def SourceSuffixPost
    (denominators : M31Vec) (backend : ZMod P)
    (out : Slice M31) : Prop :=
  out.val.length = denominators.val.length ∧
  SourceCanonicalSlice out ∧
  ∀ index, index < denominators.val.length →
    m31Value out.val[index]! =
      prefixProduct denominators index * backend *
        suffixProduct denominators (index + 1)

/-- The unchanged production reverse-range loop writes every common-backend
inverse value in the exact source order. -/
theorem source_suffix_loop_exact
    (denominators : M31Vec)
    (iter : core.iter.adapters.rev.Rev
      (core.ops.range.Range Std.Usize))
    (out : Slice M31) (inverse : M31) (backend : ZMod P)
    (hinvariant : SourceSuffixInvariant denominators backend
      (iter, out, inverse)) :
    V5CoordinateSelectedProductionSource.field.m31_batch_inverse_with_loop1
        iter ⟨denominators.val, denominators.property⟩ out inverse
      ⦃ result => SourceSuffixPost denominators backend result ⦄ := by
  unfold V5CoordinateSelectedProductionSource.field.m31_batch_inverse_with_loop1
  apply loop.spec_decr_nat
    (fun state => state.1.iter.«end».val)
    (SourceSuffixInvariant denominators backend)
    (SourceSuffixPost denominators backend)
  · rintro ⟨currentIter, currentOut, currentInverse⟩ hstate
    rcases hstate with
      ⟨hiter, hsuffixLe, hlength, hcanonical, hinverseValue,
        hprefix, houtput⟩
    simp only at hiter hsuffixLe hlength hcanonical hinverseValue hprefix houtput
    unfold
      V5CoordinateSelectedProductionSource.field.m31_batch_inverse_with_loop1.body
    simp only
    let suffix := currentIter.iter.«end»
    have hsuffixLe' : suffix.val ≤ denominators.val.length := by
      simpa [suffix] using hsuffixLe
    by_cases hactive : 0 < suffix.val
    · let previous := sourcePrevious suffix hactive
      have hpreviousValue : previous.val = suffix.val - 1 :=
        sourcePrevious_val suffix hactive
      have hpreviousLt : previous.val < suffix.val := by
        rw [hpreviousValue]
        omega
      have hpreviousBound : previous.val < denominators.val.length := by
        omega
      have houtBound : previous.val < currentOut.val.length := by
        rwa [hlength]
      have hrevRun :
          core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
              (core.ops.range.Range.Insts.DoubleEndedIterator
                core.iter.range.StepUsize) currentIter =
            .ok (some previous, sourceRevRange previous) := by
        rw [hiter]
        exact source_rev_range_next_some suffix hactive
      obtain ⟨prefixRaw, hprefixRun, hprefixRawEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (Slice.index_usize_spec currentOut previous houtBound)
      have hprefixRawBang :
          prefixRaw = currentOut.val[previous.val]! := by
        rw [hprefixRawEq,
          getElemBang_eq_getElem currentOut.val previous.val houtBound]
      obtain ⟨written, hwrittenRun, hwrittenCanonical, hwrittenValue⟩ :=
        source_mul_arbitrary_corresponds
          currentOut.val[previous.val]! currentInverse
      have hwrittenRunRaw :
          V5CoordinateSelectedProductionSource.field.M31.mul
              prefixRaw currentInverse = .ok written := by
        rw [hprefixRawBang]
        exact hwrittenRun
      obtain ⟨nextOut, hupdateRun, hnextOutEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (Slice.update_spec currentOut previous written houtBound)
      let values : Slice M31 :=
        ⟨denominators.val, denominators.property⟩
      obtain ⟨denominatorRaw, hdenominatorRun, hdenominatorRawEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (Slice.index_usize_spec values previous hpreviousBound)
      have hdenominatorRawBang :
          denominatorRaw = denominators.val[previous.val]! := by
        rw [hdenominatorRawEq,
          getElemBang_eq_getElem denominators.val previous.val
            hpreviousBound]
      have hdenominatorRun' :
          Slice.index_usize
              (⟨denominators.val, denominators.property⟩ : Slice M31)
              previous = .ok denominatorRaw := by
        simpa [values] using hdenominatorRun
      obtain ⟨nextInverse, hnextInverseRun, hnextInverseCanonical,
          hnextInverseValue⟩ :=
        source_mul_arbitrary_corresponds currentInverse
          denominators.val[previous.val]!
      have hnextInverseRunRaw :
          V5CoordinateSelectedProductionSource.field.M31.mul
              currentInverse denominatorRaw = .ok nextInverse := by
        rw [hdenominatorRawBang]
        exact hnextInverseRun
      rw [hrevRun]
      simp only [bind_tc_ok]
      rw [hprefixRun]
      simp only [bind_tc_ok]
      rw [hwrittenRunRaw]
      simp only [bind_tc_ok]
      rw [hupdateRun]
      simp only [bind_tc_ok]
      rw [hdenominatorRun']
      simp only [bind_tc_ok]
      rw [hnextInverseRunRaw]
      simp only [bind_tc_ok, WP.spec_ok]
      change SourceSuffixInvariant denominators backend
          (sourceRevRange previous, nextOut, nextInverse) ∧
        previous.val < suffix.val
      refine ⟨?_, hpreviousLt⟩
      have hnextLength : nextOut.val.length = denominators.val.length := by
        rw [hnextOutEq]
        simpa [Slice.set_length] using hlength
      have hnextCanonical : SourceCanonicalSlice nextOut := by
        rw [hnextOutEq]
        exact sourceCanonicalSlice_set currentOut previous written
          hcanonical houtBound hwrittenCanonical
      have hpreviousSucc : previous.val + 1 = suffix.val := by
        rw [hpreviousValue]
        omega
      unfold SourceSuffixInvariant
      simp only [sourceRevRange]
      refine ⟨True.intro, by omega, hnextLength, hnextCanonical,
        ?_, ?_, ?_⟩
      · rw [hnextInverseValue, hinverseValue,
          source_suffixProduct_at denominators previous.val hpreviousBound,
          hpreviousSucc]
        ring
      · intro slot hslot
        have hslotOld : slot < suffix.val := by omega
        have hslotBound : slot < currentOut.val.length := by omega
        rw [hnextOutEq]
        let setValues := currentOut.val.set previous.val written
        change m31Value setValues[slot]! = prefixProduct denominators slot
        have hsetBound : slot < setValues.length := by
          simpa only [setValues, List.length_set] using hslotBound
        have hne : previous.val ≠ slot := by omega
        rw [getElemBang_eq_getElem _ _ hsetBound, List.getElem_set]
        simp [hne]
        have hold := hprefix slot hslotOld
        rw [getElemBang_eq_getElem _ _ hslotBound] at hold
        exact hold
      · intro slot hslotLower hslotUpper
        by_cases heq : slot = previous.val
        · subst slot
          rw [hnextOutEq]
          let setValues := currentOut.val.set previous.val written
          change m31Value setValues[previous.val]! =
            prefixProduct denominators previous.val * backend *
              suffixProduct denominators (previous.val + 1)
          have hsetBound : previous.val < setValues.length := by
            simpa only [setValues, List.length_set] using houtBound
          rw [getElemBang_eq_getElem _ _ hsetBound, List.getElem_set]
          simp only [if_true]
          rw [hwrittenValue,
            hprefix previous.val hpreviousLt, hinverseValue,
            hpreviousSucc]
          ring
        · have hslotOldLower : suffix.val ≤ slot := by omega
          have hslotCurrentBound : slot < currentOut.val.length := by
            rwa [hlength]
          rw [hnextOutEq]
          let setValues := currentOut.val.set previous.val written
          change m31Value setValues[slot]! =
            prefixProduct denominators slot * backend *
              suffixProduct denominators (slot + 1)
          have hsetBound : slot < setValues.length := by
            simpa only [setValues, List.length_set] using hslotCurrentBound
          have hne : previous.val ≠ slot := by
            intro hsame
            exact heq hsame.symm
          rw [getElemBang_eq_getElem _ _ hsetBound, List.getElem_set]
          simp [hne]
          have hold := houtput slot hslotOldLower hslotUpper
          rw [getElemBang_eq_getElem _ _ hslotCurrentBound] at hold
          exact hold
    · have hdone : suffix.val = 0 := by omega
      have hiterZero : currentIter = sourceRevRange 0#usize := by
        rw [hiter]
        apply congrArg sourceRevRange
        apply UScalar.eq_of_val_eq
        exact hdone
      have hrevRun :
          core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
              (core.ops.range.Range.Insts.DoubleEndedIterator
                core.iter.range.StepUsize) currentIter =
            .ok (none, currentIter) := by
        rw [hiterZero]
        exact source_rev_range_next_none
      rw [hrevRun]
      simp only [bind_tc_ok, WP.spec_ok]
      change SourceSuffixPost denominators backend currentOut
      unfold SourceSuffixPost
      rw [hdone] at houtput
      exact ⟨hlength, hcanonical, fun index hindex =>
        houtput index (Nat.zero_le index) hindex⟩
  · exact hinvariant

private def sourceEnumeratedM31 (values : M31Vec) :
    core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter M31) :=
  { iter := sourceM31Iter values 0, count := 0#usize }

def SourceBatchInversePost
    (denominators : M31Vec) (out : Slice M31) : Prop :=
  ∃ backend : ZMod P, SourceSuffixPost denominators backend out

/-- The unchanged production batch-inverse wrapper executes both proved loops
for an arbitrary pure callback.  Its output has one common backend factor; no
correctness property of the callback is assumed here. -/
theorem source_batch_inverse_wrapper_exact
    (denominators : M31Vec) (initialOut : Slice M31)
    (inverseFn : M31 → M31)
    (hnonempty : 0 < denominators.val.length)
    (hlength : initialOut.val.length = denominators.val.length)
    (houtCanonical : SourceCanonicalSlice initialOut) :
    V5CoordinateSelectedProductionSource.field.m31_batch_inverse_with
        ⟨denominators.val, denominators.property⟩ initialOut inverseFn
      ⦃ output => SourceBatchInversePost denominators output ⦄ := by
  have honeCanonical :
      AspisV5FriCoordinateFieldSemantics.canonicalM31
        V5CoordinateSelectedProductionSource.field.M31.ONE := by
    norm_num [AspisV5FriCoordinateFieldSemantics.canonicalM31,
      AspisV5FriArithmeticSemantics.canonicalM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      V5CoordinateSelectedProductionSource.field.M31.ONE]
  have hprefixInitial : SourcePrefixInvariant denominators
      (sourceEnumeratedM31 denominators, initialOut,
        V5CoordinateSelectedProductionSource.field.M31.ONE) := by
    unfold SourcePrefixInvariant sourceEnumeratedM31 sourceM31Iter
    simp only
    refine ⟨True.intro, rfl, by norm_num, hlength, houtCanonical,
      honeCanonical, ?_, ?_⟩
    · simp [prefixProduct, m31Value,
        V5CoordinateSelectedProductionSource.field.M31.ONE]
    · intro index hindex
      norm_num at hindex
  obtain ⟨⟨forward, accumulator⟩, hprefixRun, hprefixPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (source_prefix_loop_exact denominators
        (sourceEnumeratedM31 denominators) initialOut
        V5CoordinateSelectedProductionSource.field.M31.ONE hprefixInitial)
  rcases hprefixPost with
    ⟨hforwardLength, hforwardCanonical, haccumulatorCanonical,
      haccumulatorValue, hforwardPrefix⟩
  let callbackOutput := inverseFn accumulator
  let backend : ZMod P := m31Value callbackOutput
  let suffix := Slice.len
    (⟨denominators.val, denominators.property⟩ : Slice M31)
  have hsuffixValue : suffix.val = denominators.val.length := by
    rfl
  have hsuffixInitial : SourceSuffixInvariant denominators backend
      (sourceRevRange suffix, forward, callbackOutput) := by
    unfold SourceSuffixInvariant
    simp only [sourceRevRange]
    refine ⟨True.intro, by rw [hsuffixValue], hforwardLength,
      hforwardCanonical, ?_, ?_, ?_⟩
    · simp [backend, suffixProduct, hsuffixValue]
    · intro index hindex
      apply hforwardPrefix index
      rwa [hsuffixValue] at hindex
    · intro index hlower hupper
      rw [hsuffixValue] at hlower
      omega
  obtain ⟨output, hsuffixRun, hsuffixPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (source_suffix_loop_exact denominators (sourceRevRange suffix)
        forward callbackOutput backend hsuffixInitial)
  let values : Slice M31 :=
    ⟨denominators.val, denominators.property⟩
  have hlengthEq : Slice.len values = Slice.len initialOut := by
    apply UScalar.eq_of_val_eq
    simpa [values, Slice.len_val] using hlength.symm
  have hassert : massert (Slice.len values = Slice.len initialOut) = .ok () :=
    (massert_ok _).2 hlengthEq
  have hisEmpty : core.slice.Slice.is_empty values = .ok false := by
    have hne : denominators.val ≠ [] := by
      intro heq
      rw [heq] at hnonempty
      norm_num at hnonempty
    simp [core.slice.Slice.is_empty, values, hne]
  have hsliceIter : core.slice.Slice.iter values =
      .ok (sourceM31Iter denominators 0) := by
    rfl
  have henumerate :
      core.iter.traits.iterator.Iterator.enumerate.trait_default
          (core.iter.traits.iterator.IteratorSliceIter M31)
          (sourceM31Iter denominators 0) =
        .ok (sourceEnumeratedM31 denominators) := by
    rfl
  have hrev :
      core.iter.traits.iterator.Iterator.rev.trait_default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          (core.ops.range.Range.Insts.DoubleEndedIterator
            core.iter.range.StepUsize)
          { start := 0#usize, «end» := suffix } =
        .ok (sourceRevRange suffix) := by
    rfl
  unfold V5CoordinateSelectedProductionSource.field.m31_batch_inverse_with
  change
    (do
      massert (Slice.len values = Slice.len initialOut)
      let b ← core.slice.Slice.is_empty values
      if b then ok initialOut else
        let i ← core.slice.Slice.iter values
        let enumerated ←
          core.iter.traits.iterator.Iterator.enumerate.trait_default
            (core.iter.traits.iterator.IteratorSliceIter M31) i
        let (out1, accumulator1) ←
          V5CoordinateSelectedProductionSource.field.m31_batch_inverse_with_loop0
            enumerated initialOut
              V5CoordinateSelectedProductionSource.field.M31.ONE
        let inverse1 := inverseFn accumulator1
        let iter1 ←
          core.iter.traits.iterator.Iterator.rev.trait_default
            (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
            (core.ops.range.Range.Insts.DoubleEndedIterator
              core.iter.range.StepUsize)
            { start := 0#usize, «end» := Slice.len values }
        V5CoordinateSelectedProductionSource.field.m31_batch_inverse_with_loop1
          iter1 values out1 inverse1)
      ⦃ output => SourceBatchInversePost denominators output ⦄
  rw [hassert]
  simp only [bind_tc_ok]
  rw [hisEmpty]
  simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte]
  rw [hsliceIter]
  simp only [bind_tc_ok]
  rw [henumerate]
  simp only [bind_tc_ok]
  rw [hprefixRun]
  simp only [bind_tc_ok]
  change
    (do
      let iter1 ←
        core.iter.traits.iterator.Iterator.rev.trait_default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          (core.ops.range.Range.Insts.DoubleEndedIterator
            core.iter.range.StepUsize)
          { start := 0#usize, «end» := suffix }
      V5CoordinateSelectedProductionSource.field.m31_batch_inverse_with_loop1
        iter1 values forward callbackOutput)
      ⦃ output => SourceBatchInversePost denominators output ⦄
  rw [hrev]
  simp only [bind_tc_ok]
  have hsuffixRun' :
      V5CoordinateSelectedProductionSource.field.m31_batch_inverse_with_loop1
          (sourceRevRange suffix) values forward callbackOutput = .ok output := by
    simpa [values] using hsuffixRun
  rw [hsuffixRun']
  simp only [WP.spec_ok]
  exact ⟨backend, hsuffixPost⟩

private theorem source_prefix_suffix_product
    (denominators : M31Vec) (count : Nat)
    (hcount : count ≤ denominators.val.length) :
    prefixProduct denominators count * suffixProduct denominators count =
      prefixProduct denominators denominators.val.length := by
  unfold prefixProduct suffixProduct
  have hsplit := List.take_append_drop count denominators.val
  rw [List.take_length, ← List.prod_append, ← List.map_append, hsplit]

private theorem source_entry_prefix_suffix_product
    (denominators : M31Vec) (index : Nat)
    (hindex : index < denominators.val.length) :
    prefixProduct denominators index *
          m31Value denominators.val[index]! *
        suffixProduct denominators (index + 1) =
      prefixProduct denominators denominators.val.length := by
  rw [← source_prefixProduct_succ denominators index hindex]
  exact source_prefix_suffix_product denominators (index + 1) (by omega)

def SourceBatchInverseEvidence
    (denominators : M31Vec) (output : Slice M31) : Prop :=
  output.val.length = denominators.val.length ∧
  SourceCanonicalSlice output ∧
  ∀ index, index < denominators.val.length →
    m31Value output.val[index]! =
      (m31Value denominators.val[index]!)⁻¹

/-- The production first-entry multiplication check validates the common
factor from the wrapper for every slot, so every output is the true inverse.
This theorem does not assume that the injected callback is correct. -/
theorem source_checked_batch_outputs_are_exact_inverses
    (denominators : M31Vec) (output : Slice M31) (backend : ZMod P)
    (hpost : SourceSuffixPost denominators backend output)
    (hnonempty : 0 < denominators.val.length)
    (hsourceCheck :
      V5CoordinateSelectedProductionSource.field.M31.mul
          denominators.val[0]! output.val[0]! =
        .ok V5CoordinateSelectedProductionSource.field.M31.ONE) :
    SourceBatchInverseEvidence denominators output := by
  rcases hpost with ⟨hlength, hcanonical, houtput⟩
  have hcommon (slot : Nat) (hslot : slot < denominators.val.length) :
      m31Value denominators.val[slot]! * m31Value output.val[slot]! =
        prefixProduct denominators denominators.val.length * backend := by
    rw [houtput slot hslot,
      ← source_entry_prefix_suffix_product denominators slot hslot]
    ring
  obtain ⟨check, hcheckRun, _hcheckCanonical, hcheckValue⟩ :=
    source_mul_arbitrary_corresponds
      denominators.val[0]! output.val[0]!
  have hcheckEq : check =
      V5CoordinateSelectedProductionSource.field.M31.ONE := by
    rw [hsourceCheck] at hcheckRun
    exact Result.ok.inj hcheckRun.symm
  have hfirst :
      m31Value denominators.val[0]! * m31Value output.val[0]! = 1 := by
    rw [← hcheckValue, hcheckEq]
    norm_num [m31Value,
      V5CoordinateSelectedProductionSource.field.M31.ONE]
  refine ⟨hlength, hcanonical, ?_⟩
  intro index hindex
  have hproduct :
      m31Value denominators.val[index]! * m31Value output.val[index]! = 1 := by
    rw [hcommon index hindex, ← hcommon 0 hnonempty]
    exact hfirst
  have hnonzero : m31Value denominators.val[index]! ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hproduct
    exact zero_ne_one hproduct
  apply mul_left_cancel₀ hnonzero
  rw [hproduct, mul_inv_cancel₀ hnonzero]

abbrev PairVec := alloc.vec.Vec (Array M31 2#usize)
abbrev TripleVec := alloc.vec.Vec (Array M31 3#usize)

private def sourceU32SliceIter (values : Slice Std.U32) (index : Nat) :
    core.slice.iter.Iter Std.U32 :=
  { slice := values, i := index }

private theorem source_u32_slice_iter_next_some
    (values : Slice Std.U32) (index : Nat)
    (hindex : index < values.val.length) :
    core.slice.iter.IteratorSliceIter.next
        (sourceU32SliceIter values index) =
      .ok (some values.val[index]!,
        sourceU32SliceIter values (index + 1)) := by
  unfold core.slice.iter.IteratorSliceIter.next sourceU32SliceIter
  rw [dif_pos (by simpa [Slice.len_val] using hindex)]
  rw [getElemBang_eq_getElem values.val index hindex]
  rfl

private theorem source_u32_slice_iter_next_none
    (values : Slice Std.U32) (index : Nat)
    (hindex : values.val.length ≤ index) :
    core.slice.iter.IteratorSliceIter.next
        (sourceU32SliceIter values index) =
      .ok (none, sourceU32SliceIter values index) := by
  unfold core.slice.iter.IteratorSliceIter.next sourceU32SliceIter
  rw [dif_neg (by simpa [Slice.len_val] using hindex)]

private def SourcePairInvariant
    (layer : Slice Std.U32) (flat : M31Vec) (start : Nat)
    (state : core.slice.iter.Iter Std.U32 × Std.Usize × PairVec) : Prop :=
  state.1.slice.val = layer.val ∧
  state.1.i ≤ layer.val.length ∧
  state.2.1.val = start + 2 * state.1.i ∧
  state.2.2.val =
    AspisV5FriCoordinateOutputLoops.pairOutput flat start state.1.i

def SourcePairPost
    (layer : Slice Std.U32) (flat : M31Vec) (start : Nat)
    (out : Std.Usize × PairVec) : Prop :=
  out.1.val = start + 2 * layer.val.length ∧
  out.2.val =
    AspisV5FriCoordinateOutputLoops.pairOutput flat start layer.val.length

/-- The accepted full-production pair loop copies exactly two consecutive
inverse entries for every circle query, in source order. -/
theorem source_pair_output_loop_exact
    (layer : Slice Std.U32) (flat : M31Vec)
    (iter : core.slice.iter.Iter Std.U32)
    (cursor : Std.Usize) (output : PairVec) (start : Nat)
    (hiterSlice : iter.slice.val = layer.val) (hiterIndex : iter.i = 0)
    (hcursor : cursor.val = start) (houtput : output.val = [])
    (hbound : start + 2 * layer.val.length ≤ flat.val.length) :
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop2
        iter flat cursor output
      ⦃ out => SourcePairPost layer flat start out ⦄ := by
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop2
  apply loop.spec_decr_nat
    (fun state => layer.val.length - state.1.i)
    (SourcePairInvariant layer flat start)
    (SourcePairPost layer flat start)
  · rintro ⟨currentIter, currentCursor, currentOutput⟩ hstate
    rcases hstate with
      ⟨hcurrentSlice, hindexLe, hcurrentCursor, hcurrentOutput⟩
    simp only at hcurrentSlice hindexLe hcurrentCursor hcurrentOutput
    have hiterEq : currentIter =
        sourceU32SliceIter layer currentIter.i := by
      cases hcurrent : currentIter with
      | mk currentSlice currentIndex =>
          have hsliceEq : currentSlice = layer :=
            Subtype.ext (by simpa [hcurrent] using hcurrentSlice)
          subst currentSlice
          rfl
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop2.body
    by_cases hactive : currentIter.i < layer.val.length
    · have hcursorBound : currentCursor.val < flat.val.length := by omega
      have hcursorOneBound : currentCursor.val + 1 < flat.val.length := by
        omega
      have hcursorOneMax : currentCursor.val + 1 ≤ Std.Usize.max := by
        have hflatMax := flat.property
        omega
      have hcursorTwoMax : currentCursor.val + 2 ≤ Std.Usize.max := by
        have hflatMax := flat.property
        omega
      let cursorOne := Std.Usize.wrapping_add currentCursor 1#usize
      let cursorTwo := Std.Usize.wrapping_add currentCursor 2#usize
      have hcursorOne : cursorOne.val = currentCursor.val + 1 := by
        unfold cursorOne
        rw [Std.Usize.wrapping_add_val_eq, UScalar.size_UScalarTyUsize]
        apply Nat.mod_eq_of_lt
        norm_num
        have hsize : Std.Usize.size = Std.Usize.max + 1 := by
          simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
        rw [hsize]
        omega
      have hcursorTwo : cursorTwo.val = currentCursor.val + 2 := by
        unfold cursorTwo
        rw [Std.Usize.wrapping_add_val_eq, UScalar.size_UScalarTyUsize]
        apply Nat.mod_eq_of_lt
        norm_num
        have hsize : Std.Usize.size = Std.Usize.max + 1 := by
          simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
        rw [hsize]
        omega
      have hcursorOneRun : (currentCursor + 1#usize : Result Std.Usize) =
          .ok cursorOne := by
        rw [checked_add_eq_wrapping]
        · rfl
        · rw [UScalar.max_USize_eq]
          exact hcursorOneMax
      have hcursorTwoRun : (currentCursor + 2#usize : Result Std.Usize) =
          .ok cursorTwo := by
        rw [checked_add_eq_wrapping]
        · rfl
        · rw [UScalar.max_USize_eq]
          exact hcursorTwoMax
      obtain ⟨first, hfirstRun, hfirstValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec flat currentCursor hcursorBound)
      obtain ⟨second, hsecondRun, hsecondValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec flat cursorOne
            (by simpa [hcursorOne] using hcursorOneBound))
      have hfirstBang : first = flat.val[currentCursor.val]! := by
        rw [hfirstValue,
          getElemBang_eq_getElem flat.val currentCursor.val hcursorBound]
      have hsecondBang : second = flat.val[cursorOne.val]! := by
        rw [hsecondValue,
          getElemBang_eq_getElem flat.val cursorOne.val
            (by simpa [hcursorOne] using hcursorOneBound)]
      let value : Array M31 2#usize :=
        Array.make 2#usize [first, second]
      have hcapacity : currentOutput.val.length < Std.Usize.max := by
        rw [hcurrentOutput,
          AspisV5FriCoordinateOutputLoops.pairOutput,
          List.length_map, List.length_range]
        have hlayerMax := layer.property
        omega
      obtain ⟨nextOutput, hpushRun, hnextOutput⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.push_spec currentOutput value hcapacity)
      rw [hiterEq]
      simp only
      rw [source_u32_slice_iter_next_some layer currentIter.i hactive]
      simp only [bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hfirstRun]
      simp only [bind_tc_ok]
      rw [hcursorOneRun]
      simp only [bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hsecondRun]
      simp only [bind_tc_ok]
      rw [hpushRun]
      simp only [bind_tc_ok]
      rw [hcursorTwoRun]
      simp only [bind_tc_ok, WP.spec_ok]
      change SourcePairInvariant layer flat start
          (sourceU32SliceIter layer (currentIter.i + 1), cursorTwo,
            nextOutput) ∧
        layer.val.length - (currentIter.i + 1) <
          layer.val.length - currentIter.i
      refine ⟨?_, by omega⟩
      unfold SourcePairInvariant
      simp only [sourceU32SliceIter]
      refine ⟨True.intro, by omega, ?_, ?_⟩
      · rw [hcursorTwo, hcurrentCursor]
        omega
      · rw [hnextOutput, hcurrentOutput]
        unfold AspisV5FriCoordinateOutputLoops.pairOutput
          AspisV5FriCoordinateOutputLoops.pairAt value
        rw [List.range_succ, List.map_append]
        simp only [List.map_cons, List.map_nil]
        rw [hfirstBang, hsecondBang, hcursorOne, hcurrentCursor]
    · have hdone : currentIter.i = layer.val.length := by omega
      rw [hiterEq]
      simp only
      rw [source_u32_slice_iter_next_none layer currentIter.i (by omega)]
      simp only [bind_tc_ok, WP.spec_ok]
      unfold SourcePairPost
      rw [hdone] at hcurrentCursor hcurrentOutput
      exact ⟨hcurrentCursor, hcurrentOutput⟩
  · unfold SourcePairInvariant
    simp only
    refine ⟨hiterSlice, by rw [hiterIndex]; simp, ?_, ?_⟩
    · rw [hiterIndex]
      simpa using hcursor
    · rw [hiterIndex]
      simp [AspisV5FriCoordinateOutputLoops.pairOutput, houtput]

private theorem source_usize_wrapping_add_exact
    (left right : Std.Usize)
    (hbound : left.val + right.val ≤ Std.Usize.max) :
    (Std.Usize.wrapping_add left right).val = left.val + right.val := by
  rw [Std.Usize.wrapping_add_val_eq, UScalar.size_UScalarTyUsize]
  apply Nat.mod_eq_of_lt
  have hsize : Std.Usize.size = Std.Usize.max + 1 := by
    simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
  rw [hsize]
  omega

private theorem source_usize_checked_add_exact
    (left right : Std.Usize)
    (hbound : left.val + right.val ≤ Std.Usize.max) :
    (left + right : Result Std.Usize) =
      .ok (Std.Usize.wrapping_add left right) :=
  checked_add_eq_wrapping left right (by
    rw [UScalar.max_USize_eq]
    exact hbound)

private def SourceTripleInvariant
    (layer : Slice Std.U32) (flat : M31Vec) (start : Nat)
    (state : core.slice.iter.Iter Std.U32 × Std.Usize × TripleVec) : Prop :=
  state.1.slice.val = layer.val ∧
  state.1.i ≤ layer.val.length ∧
  state.2.1.val = start + 3 * state.1.i ∧
  state.2.2.val =
    AspisV5FriCoordinateOutputLoops.tripleOutput flat start state.1.i

def SourceTriplePost
    (layer : Slice Std.U32) (flat : M31Vec) (start : Nat)
    (out : Std.Usize × TripleVec) : Prop :=
  out.1.val = start + 3 * layer.val.length ∧
  out.2.val =
    AspisV5FriCoordinateOutputLoops.tripleOutput flat start layer.val.length

/-- The full-production later-layer closure copies exactly three consecutive
inverse entries for every query, preserving both layer and query order. -/
theorem source_triple_output_loop_exact
    (layer : Slice Std.U32) (flat : M31Vec)
    (iter : core.slice.iter.Iter Std.U32)
    (cursor : Std.Usize) (output : TripleVec) (start : Nat)
    (hiterSlice : iter.slice.val = layer.val) (hiterIndex : iter.i = 0)
    (hcursor : cursor.val = start) (houtput : output.val = [])
    (hbound : start + 3 * layer.val.length ≤ flat.val.length) :
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut_loop
        iter flat cursor output
      ⦃ out => SourceTriplePost layer flat start out ⦄ := by
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut_loop
  apply loop.spec_decr_nat
    (fun state => layer.val.length - state.1.i)
    (SourceTripleInvariant layer flat start)
    (SourceTriplePost layer flat start)
  · rintro ⟨currentIter, currentCursor, currentOutput⟩ hstate
    rcases hstate with
      ⟨hcurrentSlice, hindexLe, hcurrentCursor, hcurrentOutput⟩
    simp only at hcurrentSlice hindexLe hcurrentCursor hcurrentOutput
    have hiterEq : currentIter =
        sourceU32SliceIter layer currentIter.i := by
      cases hcurrent : currentIter with
      | mk currentSlice currentIndex =>
          have hsliceEq : currentSlice = layer :=
            Subtype.ext (by simpa [hcurrent] using hcurrentSlice)
          subst currentSlice
          rfl
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut_loop.body
    by_cases hactive : currentIter.i < layer.val.length
    · have hcursor0Bound : currentCursor.val < flat.val.length := by omega
      have hcursor1Bound : currentCursor.val + 1 < flat.val.length := by omega
      have hcursor2Bound : currentCursor.val + 2 < flat.val.length := by omega
      have hcursor1Max : currentCursor.val + 1 ≤ Std.Usize.max := by
        have hflatMax := flat.property
        omega
      have hcursor2Max : currentCursor.val + 2 ≤ Std.Usize.max := by
        have hflatMax := flat.property
        omega
      have hcursor3Max : currentCursor.val + 3 ≤ Std.Usize.max := by
        have hflatMax := flat.property
        omega
      let cursor1 := Std.Usize.wrapping_add currentCursor 1#usize
      let cursor2 := Std.Usize.wrapping_add currentCursor 2#usize
      let cursor3 := Std.Usize.wrapping_add currentCursor 3#usize
      have hcursor1 : cursor1.val = currentCursor.val + 1 := by
        unfold cursor1
        apply source_usize_wrapping_add_exact
        simpa using hcursor1Max
      have hcursor2 : cursor2.val = currentCursor.val + 2 := by
        unfold cursor2
        apply source_usize_wrapping_add_exact
        simpa using hcursor2Max
      have hcursor3 : cursor3.val = currentCursor.val + 3 := by
        unfold cursor3
        apply source_usize_wrapping_add_exact
        simpa using hcursor3Max
      have hcursor1Run : (currentCursor + 1#usize : Result Std.Usize) =
          .ok cursor1 := by
        unfold cursor1
        apply source_usize_checked_add_exact
        simpa using hcursor1Max
      have hcursor2Run : (currentCursor + 2#usize : Result Std.Usize) =
          .ok cursor2 := by
        unfold cursor2
        apply source_usize_checked_add_exact
        simpa using hcursor2Max
      have hcursor3Run : (currentCursor + 3#usize : Result Std.Usize) =
          .ok cursor3 := by
        unfold cursor3
        apply source_usize_checked_add_exact
        simpa using hcursor3Max
      obtain ⟨first, hfirstRun, hfirstValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec flat currentCursor hcursor0Bound)
      obtain ⟨second, hsecondRun, hsecondValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec flat cursor1
            (by simpa [hcursor1] using hcursor1Bound))
      obtain ⟨third, hthirdRun, hthirdValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec flat cursor2
            (by simpa [hcursor2] using hcursor2Bound))
      have hfirstBang : first = flat.val[currentCursor.val]! := by
        rw [hfirstValue,
          getElemBang_eq_getElem flat.val currentCursor.val hcursor0Bound]
      have hsecondBang : second = flat.val[cursor1.val]! := by
        rw [hsecondValue,
          getElemBang_eq_getElem flat.val cursor1.val
            (by simpa [hcursor1] using hcursor1Bound)]
      have hthirdBang : third = flat.val[cursor2.val]! := by
        rw [hthirdValue,
          getElemBang_eq_getElem flat.val cursor2.val
            (by simpa [hcursor2] using hcursor2Bound)]
      let value : Array M31 3#usize :=
        Array.make 3#usize [first, second, third]
      have hcapacity : currentOutput.val.length < Std.Usize.max := by
        rw [hcurrentOutput,
          AspisV5FriCoordinateOutputLoops.tripleOutput,
          List.length_map, List.length_range]
        have hlayerMax := layer.property
        omega
      obtain ⟨nextOutput, hpushRun, hnextOutput⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.push_spec currentOutput value hcapacity)
      rw [hiterEq]
      simp only
      rw [source_u32_slice_iter_next_some layer currentIter.i hactive]
      simp only [bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hfirstRun]
      simp only [bind_tc_ok]
      rw [hcursor1Run]
      simp only [bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hsecondRun]
      simp only [bind_tc_ok]
      rw [hcursor2Run]
      simp only [bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hthirdRun]
      simp only [bind_tc_ok]
      rw [hpushRun]
      simp only [bind_tc_ok]
      rw [hcursor3Run]
      simp only [bind_tc_ok, WP.spec_ok]
      change SourceTripleInvariant layer flat start
          (sourceU32SliceIter layer (currentIter.i + 1), cursor3,
            nextOutput) ∧
        layer.val.length - (currentIter.i + 1) <
          layer.val.length - currentIter.i
      refine ⟨?_, by omega⟩
      unfold SourceTripleInvariant
      simp only [sourceU32SliceIter]
      refine ⟨True.intro, by omega, ?_, ?_⟩
      · rw [hcursor3, hcurrentCursor]
        omega
      · rw [hnextOutput, hcurrentOutput]
        unfold AspisV5FriCoordinateOutputLoops.tripleOutput
          AspisV5FriCoordinateOutputLoops.tripleAt value
        rw [List.range_succ, List.map_append]
        simp only [List.map_cons, List.map_nil]
        rw [hfirstBang, hsecondBang, hthirdBang,
          hcursor1, hcursor2, hcurrentCursor]
    · have hdone : currentIter.i = layer.val.length := by omega
      rw [hiterEq]
      simp only
      rw [source_u32_slice_iter_next_none layer currentIter.i (by omega)]
      simp only [bind_tc_ok, WP.spec_ok]
      unfold SourceTriplePost
      rw [hdone] at hcurrentCursor hcurrentOutput
      exact ⟨hcurrentCursor, hcurrentOutput⟩
  · unfold SourceTripleInvariant
    simp only
    refine ⟨hiterSlice, by rw [hiterIndex]; simp, ?_, ?_⟩
    · rw [hiterIndex]
      simpa using hcursor
    · rw [hiterIndex]
      simp [AspisV5FriCoordinateOutputLoops.tripleOutput, houtput]

/-- One mutable closure call used by `array::from_fn` returns the exact
three-entry groups for the selected later layer and threads only the cursor. -/
theorem source_triple_closure_call_exact
    (later : Array (Slice Std.U32) 3#usize) (flat : M31Vec)
    (cursor ordinal : Std.Usize) (layer : Slice Std.U32) (start : Nat)
    (hlayer : Array.index_usize later ordinal = .ok layer)
    (hcursor : cursor.val = start)
    (hbound : start + 3 * layer.val.length ≤ flat.val.length) :
    ∃ (values : TripleVec) (nextCursor : Std.Usize),
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut_trait
          (later, flat, cursor) ordinal =
        .ok (values, (later, flat, nextCursor)) ∧
      SourceTriplePost layer flat start (nextCursor, values) := by
  let empty : TripleVec :=
    alloc.vec.Vec.with_capacity (Array M31 3#usize) (Slice.len layer)
  have hempty : empty.val = [] := rfl
  let iter := sourceU32SliceIter layer 0
  obtain ⟨⟨nextCursor, values⟩, hloop, hpost⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (source_triple_output_loop_exact layer flat iter cursor empty start
        (by rfl) (by rfl) hcursor hempty hbound)
  have hinto :
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
          layer = .ok iter := by
    rfl
  have hloop' :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut_loop
          iter flat cursor empty = .ok (nextCursor, values) := hloop
  refine ⟨values, nextCursor, ?_, hpost⟩
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut_trait
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313.call_mut
  simp only
  rw [hlayer]
  simp only [bind_tc_ok]
  rw [hinto]
  simp only [bind_tc_ok]
  rw [hloop']
  rfl

/-- The production `array::from_fn` call invokes the mutable later-layer
closure exactly at ordinals zero, one, and two.  The returned array therefore
contains the three consecutive groups from the flat inverse vector, and the
captured cursor advances by exactly their total width. -/
theorem source_later_from_fn_exact
    (later : Array (Slice Std.U32) 3#usize) (flat : M31Vec)
    (cursor : Std.Usize) (line0 line1 line2 : Slice Std.U32) (start : Nat)
    (hline0 : Array.index_usize later 0#usize = .ok line0)
    (hline1 : Array.index_usize later 1#usize = .ok line1)
    (hline2 : Array.index_usize later 2#usize = .ok line2)
    (hcursor : cursor.val = start)
    (hbound : start + 3 * line0.val.length + 3 * line1.val.length +
        3 * line2.val.length ≤ flat.val.length) :
    ∃ (values0 values1 values2 : TripleVec) (nextCursor : Std.Usize),
      core.array.from_fn 3#usize
          V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313
          (later, flat, cursor) =
        .ok (Array.make 3#usize [values0, values1, values2],
          (later, flat, nextCursor)) ∧
      values0.val =
        AspisV5FriCoordinateOutputLoops.tripleOutput flat start
          line0.val.length ∧
      values1.val =
        AspisV5FriCoordinateOutputLoops.tripleOutput flat
          (start + 3 * line0.val.length) line1.val.length ∧
      values2.val =
        AspisV5FriCoordinateOutputLoops.tripleOutput flat
          (start + 3 * line0.val.length + 3 * line1.val.length)
          line2.val.length ∧
      nextCursor.val = start + 3 * line0.val.length +
        3 * line1.val.length + 3 * line2.val.length := by
  obtain ⟨values0, cursor1, hcall0, hpost0⟩ :=
    source_triple_closure_call_exact later flat cursor 0#usize line0 start
      hline0 hcursor (by omega)
  rcases hpost0 with ⟨hcursor1, hvalues0⟩
  obtain ⟨values1, cursor2, hcall1, hpost1⟩ :=
    source_triple_closure_call_exact later flat cursor1 1#usize line1
      (start + 3 * line0.val.length) hline1 hcursor1 (by omega)
  rcases hpost1 with ⟨hcursor2, hvalues1⟩
  obtain ⟨values2, cursor3, hcall2, hpost2⟩ :=
    source_triple_closure_call_exact later flat cursor2 2#usize line2
      (start + 3 * line0.val.length + 3 * line1.val.length)
      hline2 hcursor2 (by omega)
  rcases hpost2 with ⟨hcursor3, hvalues2⟩
  refine ⟨values0, values1, values2, cursor3, ?_, hvalues0,
    hvalues1, hvalues2, hcursor3⟩
  unfold core.array.from_fn
  simp only [if_pos rfl, bind_tc_ok]
  rw [hcall0]
  simp only [bind_tc_ok]
  rw [hcall1]
  simp only [bind_tc_ok]
  rw [hcall2]
  rfl

private def sourcePointSliceIter (values : PointVec) (index : Nat) :
    core.slice.iter.Iter Point :=
  { slice := alloc.vec.Vec.deref values, i := index }

private theorem source_point_slice_iter_next_some
    (values : PointVec) (index : Nat)
    (hindex : index < values.val.length) :
    core.slice.iter.IteratorSliceIter.next
        (sourcePointSliceIter values index) =
      .ok (some values.val[index]!,
        sourcePointSliceIter values (index + 1)) := by
  unfold core.slice.iter.IteratorSliceIter.next sourcePointSliceIter
  rw [dif_pos (by change index < values.val.length; exact hindex)]
  rw [getElemBang_eq_getElem values.val index hindex]
  rfl

private theorem source_point_slice_iter_next_none
    (values : PointVec) (index : Nat)
    (hindex : values.val.length ≤ index) :
    core.slice.iter.IteratorSliceIter.next
        (sourcePointSliceIter values index) =
      .ok (none, sourcePointSliceIter values index) := by
  unfold core.slice.iter.IteratorSliceIter.next sourcePointSliceIter
  rw [dif_neg (by change ¬ index < values.val.length; omega)]

def SourceFinalXFormula (x : M31) : ZMod P :=
  2 * (2 * m31Value x ^ 2 - 1) ^ 2 - 1

def SourceFinalXListPost (points : PointVec) (output : List M31) : Prop :=
  output.length = points.val.length ∧
  (∀ value, value ∈ output →
    AspisV5FriCoordinateFieldSemantics.canonicalM31 value) ∧
  ∀ index, index < points.val.length →
    m31Value output[index]! = SourceFinalXFormula points.val[index]!.x

def SourceFinalXPost (points : PointVec) (output : M31Vec) : Prop :=
  output.val.length = points.val.length ∧
  (∀ index, index < output.val.length →
    AspisV5FriCoordinateFieldSemantics.canonicalM31 output.val[index]!) ∧
  ∀ index, index < points.val.length →
    m31Value output.val[index]! = SourceFinalXFormula points.val[index]!.x

private def SourceFinalXAccumulatorInvariant
    (points : PointVec) (index : Nat) (accumulator : List M31) : Prop :=
  index ≤ points.val.length ∧
  accumulator.length = index ∧
  (∀ value, value ∈ accumulator →
    AspisV5FriCoordinateFieldSemantics.canonicalM31 value) ∧
  ∀ ordinal, ordinal < index →
    m31Value accumulator.reverse[ordinal]! =
      SourceFinalXFormula points.val[ordinal]!.x

/-- The standard-library iterator collector reached by the unchanged source
maps every point, in order, through the source closure which applies
`double_x` twice.  This theorem follows the actual partial iterator model,
including its reversed accumulator. -/
theorem source_final_x_iter_to_list_exact
    (points : PointVec) (index : Nat) (accumulator : List M31)
    (hpoints : ∀ ordinal, ordinal < points.val.length →
      AspisV5FriCoordinateFieldSemantics.canonicalM31
        points.val[ordinal]!.x)
    (hinvariant :
      SourceFinalXAccumulatorInvariant points index accumulator) :
    ∃ output : List M31,
      alloc.vec.FromIteratorVec.iterToList
          (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
            (core.iter.traits.iterator.IteratorSliceIter Point)
            V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31)
          ⟨sourcePointSliceIter points index, ()⟩ accumulator =
        .ok output ∧
      SourceFinalXListPost points output := by
  rcases hinvariant with
    ⟨hindexLe, haccumulatorLength, haccumulatorCanonical,
      haccumulatorValues⟩
  rw [alloc.vec.FromIteratorVec.iterToList.eq_1]
  by_cases hactive : index < points.val.length
  · simp only [
      core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next]
    rw [source_point_slice_iter_next_some points index hactive]
    simp only [bind_tc_ok]
    have hpointCanonical :
        AspisV5FriCoordinateFieldSemantics.canonicalM31
          points.val[index]!.x :=
      hpoints index hactive
    obtain ⟨first, hfirst, hfirstCanonical, hfirstValue⟩ :=
      source_double_x_produces_canonical points.val[index]!.x
        hpointCanonical
    obtain ⟨second, hsecond, hsecondCanonical, hsecondValue⟩ :=
      source_double_x_produces_canonical first hfirstCanonical
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31.call_mut
    rw [hfirst]
    simp only [bind_tc_ok]
    rw [hsecond]
    simp only [bind_tc_ok]
    have hnextInvariant :
        SourceFinalXAccumulatorInvariant points (index + 1)
          (second :: accumulator) := by
      unfold SourceFinalXAccumulatorInvariant
      refine ⟨by omega, by simp [haccumulatorLength], ?_, ?_⟩
      · intro value hmember
        simp only [List.mem_cons] at hmember
        rcases hmember with rfl | hmember
        · exact hsecondCanonical
        · exact haccumulatorCanonical value hmember
      · intro ordinal hordinal
        rw [List.reverse_cons]
        by_cases hold : ordinal < index
        · rw [getElemBang_append_left accumulator.reverse [second] ordinal]
          · exact haccumulatorValues ordinal hold
          · simpa [haccumulatorLength] using hold
        · have hlast : ordinal = index := by omega
          subst ordinal
          have hreverseLength : accumulator.reverse.length = index := by
            simpa [haccumulatorLength]
          rw [getElemBang_eq_getElem _ index (by simp [hreverseLength])]
          simp [hreverseLength, hsecondValue, hfirstValue,
            SourceFinalXFormula]
    obtain ⟨output, hrun, hpost⟩ :=
      source_final_x_iter_to_list_exact points (index + 1)
        (second :: accumulator) hpoints hnextInvariant
    exact ⟨output, hrun, hpost⟩
  · have hdone : index = points.val.length := by omega
    simp only [
      core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next]
    rw [source_point_slice_iter_next_none points index (by omega)]
    simp only [bind_tc_ok]
    refine ⟨accumulator.reverse, rfl, ?_⟩
    unfold SourceFinalXListPost
    refine ⟨by simp [haccumulatorLength, hdone], ?_, ?_⟩
    · intro value hmember
      exact haccumulatorCanonical value (by simpa using hmember)
    · intro ordinal hordinal
      exact haccumulatorValues ordinal (by simpa [hdone] using hordinal)
termination_by points.val.length - index
decreasing_by omega

/-- The exact `slice.iter().map(...).collect::<Vec<_>>()` expression used by
the production function returns one canonical twice-doubled x coordinate per
input point, without omission, duplication, or reordering. -/
theorem source_final_x_collect_exact
    (points : PointVec)
    (hpoints : ∀ ordinal, ordinal < points.val.length →
      AspisV5FriCoordinateFieldSemantics.canonicalM31
        points.val[ordinal]!.x) :
    ∃ output : M31Vec,
      (do
        let iter ← core.slice.Slice.iter (alloc.vec.Vec.deref points)
        let mapped ←
          core.iter.traits.iterator.Iterator.map.default
            (core.iter.traits.iterator.IteratorSliceIter Point)
            V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31
            iter ()
        core.iter.traits.iterator.Iterator.collect.default
          (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
            (core.iter.traits.iterator.IteratorSliceIter Point)
            V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31)
          (core.iter.traits.collect.FromIteratorVec M31) mapped) =
        .ok output ∧
      SourceFinalXPost points output := by
  have hinvariant :
      SourceFinalXAccumulatorInvariant points 0 [] := by
    unfold SourceFinalXAccumulatorInvariant
    simp
  obtain ⟨values, hvaluesRun, hvaluesPost⟩ :=
    source_final_x_iter_to_list_exact points 0 [] hpoints hinvariant
  rcases hvaluesPost with ⟨hvaluesLength, hvaluesCanonical, hvalues⟩
  have hcapacity : values.length ≤ Std.Usize.max := by
    rw [hvaluesLength]
    exact points.property
  let output : M31Vec := ⟨values, hcapacity⟩
  have hvaluesRun' :
      alloc.vec.FromIteratorVec.iterToList
          (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
            (core.iter.traits.iterator.IteratorSliceIter Point)
            V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31)
          ⟨⟨alloc.vec.Vec.deref points, 0⟩, ()⟩ [] = .ok values := by
    simpa [sourcePointSliceIter] using hvaluesRun
  refine ⟨output, ?_, ?_⟩
  · simp only [core.slice.Slice.iter, bind_tc_ok,
      core.iter.traits.iterator.Iterator.map.default]
    unfold core.iter.traits.iterator.Iterator.collect.default
      core.iter.traits.collect.FromIteratorVec
      alloc.vec.FromIteratorVec.from_iter
    simp only [
      core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_tc_ok]
    rw [hvaluesRun']
    simp only [bind_tc_ok, dif_pos hcapacity]
    rfl
  · unfold SourceFinalXPost output
    refine ⟨hvaluesLength, ?_, hvalues⟩
    intro index hindex
    apply hvaluesCanonical values[index]!
    rw [getElemBang_eq_getElem values index hindex]
    exact List.getElem_mem hindex

def SourceOutputEvidence
    (layer0 line0 line1 line2 : Slice Std.U32)
    (flat : M31Vec) (line3Points : PointVec) (output : Output) : Prop :=
  output.circle.val =
      AspisV5FriCoordinateOutputLoops.pairOutput flat 0
        layer0.val.length ∧
  ∃ values0 values1 values2 : TripleVec,
    output.later.val = [values0, values1, values2] ∧
    values0.val = AspisV5FriCoordinateOutputLoops.tripleOutput flat
      (2 * layer0.val.length) line0.val.length ∧
    values1.val = AspisV5FriCoordinateOutputLoops.tripleOutput flat
      (2 * layer0.val.length + 3 * line0.val.length) line1.val.length ∧
    values2.val = AspisV5FriCoordinateOutputLoops.tripleOutput flat
      (2 * layer0.val.length + 3 * line0.val.length +
        3 * line1.val.length) line2.val.length ∧
    SourceFinalXPost line3Points output.final_x

/-- Every output-building call in the unchanged production source has exact
layout semantics.  This includes the pair loop, the mutable `array::from_fn`
closure, its final cursor assertion, and the iterator map/collect final-x
path. -/
theorem source_output_calls_exact
    (layer0 line0 line1 line2 : Slice Std.U32)
    (later : Array (Slice Std.U32) 3#usize)
    (flat : M31Vec) (line3Points : PointVec)
    (hlater0 : Array.index_usize later 0#usize = .ok line0)
    (hlater1 : Array.index_usize later 1#usize = .ok line1)
    (hlater2 : Array.index_usize later 2#usize = .ok line2)
    (hflatLength : flat.val.length = 2 * layer0.val.length +
      3 * line0.val.length + 3 * line1.val.length +
      3 * line2.val.length)
    (hline3Points : ∀ ordinal, ordinal < line3Points.val.length →
      AspisV5FriCoordinateFieldSemantics.canonicalM31
        line3Points.val[ordinal]!.x) :
    ∃ (cursor0 : Std.Usize) (circle : PairVec)
      (values0 values1 values2 : TripleVec) (cursor3 : Std.Usize)
      (finalX : M31Vec),
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0_loop2
          (sourceU32SliceIter layer0 0) flat 0#usize
          (alloc.vec.Vec.with_capacity (Array M31 2#usize)
            (Slice.len layer0)) = .ok (cursor0, circle) ∧
      core.array.from_fn 3#usize
          V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeVecArrayM313
          (later, flat, cursor0) =
        .ok (Array.make 3#usize [values0, values1, values2],
          (later, flat, cursor3)) ∧
      cursor3.val = flat.val.length ∧
      (do
        let iter ← core.slice.Slice.iter (alloc.vec.Vec.deref line3Points)
        let mapped ←
          core.iter.traits.iterator.Iterator.map.default
            (core.iter.traits.iterator.IteratorSliceIter Point)
            V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31
            iter ()
        core.iter.traits.iterator.Iterator.collect.default
          (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
            (core.iter.traits.iterator.IteratorSliceIter Point)
            V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedBaseCirclePointM31)
          (core.iter.traits.collect.FromIteratorVec M31) mapped) = .ok finalX ∧
      SourceOutputEvidence layer0 line0 line1 line2 flat line3Points
        { circle := circle,
          later := Array.make 3#usize [values0, values1, values2],
          final_x := finalX } := by
  let circleEmpty : PairVec :=
    alloc.vec.Vec.with_capacity (Array M31 2#usize) (Slice.len layer0)
  have hcircleEmpty : circleEmpty.val = [] := rfl
  obtain ⟨⟨cursor0, circle⟩, hcircleRun, hcirclePost⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (source_pair_output_loop_exact layer0 flat
        (sourceU32SliceIter layer0 0) 0#usize circleEmpty 0 rfl rfl rfl
        hcircleEmpty (by rw [hflatLength]; omega))
  rcases hcirclePost with ⟨hcursor0, hcircleValue⟩
  have hcursor0' : cursor0.val = 2 * layer0.val.length := by
    simpa using hcursor0
  obtain ⟨values0, values1, values2, cursor3, hlaterRun,
    hvalues0, hvalues1, hvalues2, hcursor3⟩ :=
      source_later_from_fn_exact later flat cursor0 line0 line1 line2
        (2 * layer0.val.length) hlater0 hlater1 hlater2 hcursor0'
        (by rw [hflatLength])
  obtain ⟨finalX, hfinalRun, hfinalPost⟩ :=
    source_final_x_collect_exact line3Points hline3Points
  refine ⟨cursor0, circle, values0, values1, values2, cursor3, finalX,
    by simpa [circleEmpty] using hcircleRun, hlaterRun, ?_, hfinalRun, ?_⟩
  · rw [hcursor3, hflatLength]
  · unfold SourceOutputEvidence
    refine ⟨hcircleValue, values0, values1, values2, rfl,
      hvalues0, hvalues1, hvalues2, hfinalPost⟩

private theorem source_extend_pair_exact
    (values : M31Vec) (left right : M31)
    (hcapacity : values.val.length + 2 ≤ Std.Usize.max) :
    ∃ output : M31Vec,
      alloc.vec.Vec.extend_from_slice
          V5CoordinateSelectedProductionSource.field.M31.Insts.CoreCloneClone
          values
          (Array.to_slice (Array.make 2#usize [left, right])) = .ok output ∧
      output.val = values.val ++ [left, right] := by
  let slice : Slice M31 := Array.to_slice
    (Array.make 2#usize [left, right])
  have hslice : slice.val = [left, right] := rfl
  have hclone : Aeneas.Std.WP.spec
      (Slice.clone
        V5CoordinateSelectedProductionSource.field.M31.Insts.CoreCloneClone.clone
        slice) (fun cloned => slice = cloned) := by
    apply Slice.clone_spec
    intro value hvalue
    unfold
      V5CoordinateSelectedProductionSource.field.M31.Insts.CoreCloneClone.clone
    rfl
  obtain ⟨cloned, hcloneRun, hcloned⟩ :=
    Aeneas.Std.WP.spec_imp_exists hclone
  subst cloned
  let output : M31Vec :=
    ⟨values.val ++ slice.val, by
      rw [List.length_append, hslice]
      simpa using hcapacity⟩
  refine ⟨output, ?_, ?_⟩
  · change alloc.vec.Vec.extend_from_slice
      V5CoordinateSelectedProductionSource.field.M31.Insts.CoreCloneClone
      values slice = .ok output
    unfold alloc.vec.Vec.extend_from_slice
    have hlength : values.length + slice.length ≤ Std.Usize.max := by
      simpa [alloc.vec.Vec.length, Slice.length, hslice] using hcapacity
    rw [dif_pos hlength]
    simp only [hcloneRun]
    rfl
  · simp [output, hslice]

private def SourceCircleInvariant (points : PointVec) (ordinal : Nat)
    (values : M31Vec) : Prop :=
  ordinal ≤ points.val.length ∧
  values.val.length = 2 * ordinal ∧
  SourceCanonicalM31Vec values ∧
  ∀ index, index < ordinal →
    m31Value values.val[2 * index]! =
        2 * m31Value points.val[index]!.x ∧
    m31Value values.val[2 * index + 1]! =
        2 * m31Value points.val[index]!.y

def SourceCirclePost (points : PointVec) (values : M31Vec) : Prop :=
  values.val.length = 2 * points.val.length ∧
  SourceCanonicalM31Vec values ∧
  ∀ index, index < points.val.length →
    m31Value values.val[2 * index]! =
        2 * m31Value points.val[index]!.x ∧
    m31Value values.val[2 * index + 1]! =
        2 * m31Value points.val[index]!.y

/-- The actual production circle-prefix loop appends exactly `2*x, 2*y`
for every selected circle point.  The theorem also exposes the exact vector
passed to the later-line loop, so the two generated source loops can be
composed without an implementation premise. -/
theorem source_circle_prefix_loop_exact
    (points : PointVec) (ordinal : Nat) (values : M31Vec)
    (iter : core.slice.iter.Iter Point)
    (layer0 : Slice Std.U32) (later : Array (Slice Std.U32) 3#usize)
    (inverseFn : M31 → M31) (line1 line2 line3 : PointVec)
    (denominatorCount : Std.Usize)
    (hiter : iter = sourcePointSliceIter points ordinal)
    (hpoints : SourceCanonicalPoints points)
    (hnonzero : ∀ index, index < points.val.length →
      2 * m31Value points.val[index]!.x ≠ 0 ∧
      2 * m31Value points.val[index]!.y ≠ 0)
    (hcapacity : 2 * points.val.length ≤ Std.Usize.max)
    (hinvariant : SourceCircleInvariant points ordinal values) :
    ∃ after : M31Vec,
      SourceCirclePost points after ∧
      ∀ result,
        V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0
            iter layer0 later inverseFn line1 line2 line3 denominatorCount
            values = .ok result →
        V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
            ⟨Array.make 3#usize [line1, line2, line3], 0⟩ layer0 later
            inverseFn line3 denominatorCount after = .ok result := by
  rcases hinvariant with
    ⟨hordinalLe, hlength, hcanonical, hvalues⟩
  by_cases hactive : ordinal < points.val.length
  · have hpointCanonical := hpoints ordinal hactive
    obtain ⟨x, hxRun, hxCanonical, hxValue⟩ :=
      source_double_produces_canonical points.val[ordinal]!.x
        hpointCanonical.1
    obtain ⟨y, hyRun, hyCanonical, hyValue⟩ :=
      source_double_produces_canonical points.val[ordinal]!.y
        hpointCanonical.2
    have hxyNonzero := hnonzero ordinal hactive
    have hxNonzero : m31Value x ≠ 0 := by
      rw [hxValue]
      exact hxyNonzero.1
    have hyNonzero : m31Value y ≠ 0 := by
      rw [hyValue]
      exact hxyNonzero.2
    have hxZero := source_is_zero_false x hxNonzero
    have hyZero := source_is_zero_false y hyNonzero
    have hpairCapacity : values.val.length + 2 ≤ Std.Usize.max := by
      rw [hlength]
      omega
    obtain ⟨next, hnextRun, hnextValue⟩ :=
      source_extend_pair_exact values x y hpairCapacity
    have hnextInvariant :
        SourceCircleInvariant points (ordinal + 1) next := by
      unfold SourceCircleInvariant
      refine ⟨by omega, ?_, ?_, ?_⟩
      · rw [hnextValue, List.length_append, hlength]
        simp
        omega
      · intro value hmember
        rw [hnextValue] at hmember
        rcases List.mem_append.mp hmember with hmember | hmember
        · exact hcanonical value hmember
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
          rcases hmember with rfl | rfl
          · exact hxCanonical
          · exact hyCanonical
      · intro index hindex
        by_cases hold : index < ordinal
        · have holdPair := hvalues index hold
          have hleftBound : 2 * index < values.val.length := by omega
          have hrightBound : 2 * index + 1 < values.val.length := by omega
          have hleftNext :
              next.val[2 * index]! = values.val[2 * index]! := by
            rw [hnextValue]
            exact getElemBang_append_left values.val [x, y] (2 * index)
              hleftBound
          have hrightNext :
              next.val[2 * index + 1]! =
                values.val[2 * index + 1]! := by
            rw [hnextValue]
            exact getElemBang_append_left values.val [x, y]
              (2 * index + 1) hrightBound
          rw [hleftNext, hrightNext]
          exact holdPair
        · have hnew : index = ordinal := by omega
          subst index
          have hxAt : next.val[2 * ordinal]! = x := by
            have hslot : 2 * ordinal = values.val.length := hlength.symm
            rw [hnextValue, hslot]
            simp
          have hyAt : next.val[2 * ordinal + 1]! = y := by
            have hslot : 2 * ordinal + 1 = values.val.length + 1 := by
              omega
            rw [hnextValue, hslot]
            simp
          rw [hxAt, hyAt, hxValue, hyValue]
          exact ⟨rfl, rfl⟩
    obtain ⟨after, hafter, hcontinue⟩ :=
      source_circle_prefix_loop_exact points (ordinal + 1) next
        (sourcePointSliceIter points (ordinal + 1)) layer0 later inverseFn
        line1 line2 line3 denominatorCount rfl hpoints hnonzero hcapacity
        hnextInvariant
    refine ⟨after, hafter, ?_⟩
    intro result hresult
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0
      at hresult
    rw [loop.eq_1] at hresult
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0.body
      at hresult
    simp only at hresult
    rw [hiter, source_point_slice_iter_next_some points ordinal hactive]
      at hresult
    simp only [bind_tc_ok] at hresult
    rw [hxRun] at hresult
    simp only [bind_tc_ok] at hresult
    rw [hyRun] at hresult
    simp only [bind_tc_ok] at hresult
    rw [hxZero] at hresult
    simp only [bind_tc_ok, Bool.false_eq_true, if_false] at hresult
    rw [hyZero] at hresult
    simp only [bind_tc_ok, Bool.false_eq_true, if_false, Std.lift]
      at hresult
    rw [hnextRun] at hresult
    simp only [bind_tc_ok] at hresult
    have hnextAccepted :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0
          (sourcePointSliceIter points (ordinal + 1)) layer0 later
          inverseFn line1 line2 line3 denominatorCount next = .ok result := by
      exact hresult
    exact hcontinue result hnextAccepted
  · have hdone : ordinal = points.val.length := by omega
    refine ⟨values, ?_, ?_⟩
    · unfold SourceCirclePost
      rw [hdone] at hlength hvalues
      exact ⟨hlength, hcanonical, hvalues⟩
    · intro result hresult
      unfold
        V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0
        at hresult
      let terminal :=
        V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
          ⟨Array.make 3#usize [line1, line2, line3], 0⟩ layer0 later
          inverseFn line3 denominatorCount values
      have hterminalBody :
          V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0.body
              layer0 later inverseFn line1 line2 line3 denominatorCount
              iter values = (do
            let value ← terminal
            Result.ok (.done value)) := by
        unfold
          V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0.body
        rw [hiter,
          source_point_slice_iter_next_none points ordinal (by omega)]
        rfl
      exact source_loop_terminal_accepted
        (fun state =>
          V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0.body
            layer0 later inverseFn line1 line2 line3 denominatorCount
            state.1 state.2)
        (iter, values) terminal result hterminalBody hresult
termination_by points.val.length - ordinal
decreasing_by omega

/-- Specialisation of the proved circle-prefix loop to the actual production
entry state: the iterator starts at zero and the denominator vector is the
empty vector allocated with the source-supplied capacity.  This public wrapper
keeps the private recursive invariant out of the high-level composition
module. -/
theorem source_circle_prefix_from_empty_accepted
    (points : PointVec)
    (layer0 : Slice Std.U32) (later : Array (Slice Std.U32) 3#usize)
    (inverseFn : M31 → M31) (line1 line2 line3 : PointVec)
    (denominatorCount : Std.Usize)
    (hpoints : SourceCanonicalPoints points)
    (hnonzero : ∀ index, index < points.val.length →
      2 * m31Value points.val[index]!.x ≠ 0 ∧
      2 * m31Value points.val[index]!.y ≠ 0)
    (hcapacity : 2 * points.val.length ≤ Std.Usize.max) :
    ∃ after : M31Vec,
      SourceCirclePost points after ∧
      ∀ result,
        V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0
            { slice := alloc.vec.Vec.deref points, i := 0 }
            layer0 later inverseFn line1 line2 line3 denominatorCount
            (alloc.vec.Vec.with_capacity M31 denominatorCount) = .ok result →
        V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
            ⟨Array.make 3#usize [line1, line2, line3], 0⟩ layer0 later
            inverseFn line3 denominatorCount after = .ok result := by
  let initial : M31Vec :=
    alloc.vec.Vec.with_capacity M31 denominatorCount
  have hinvariant : SourceCircleInvariant points 0 initial := by
    unfold SourceCircleInvariant SourceCanonicalM31Vec initial
    simp [alloc.vec.Vec.with_capacity]
  simpa [initial, sourcePointSliceIter] using
    (source_circle_prefix_loop_exact points 0 initial
      { slice := alloc.vec.Vec.deref points, i := 0 }
      layer0 later inverseFn line1 line2 line3 denominatorCount rfl
      hpoints hnonzero hcapacity hinvariant)

def SourceTerminalEvidence
    (layer0 line0 line1 line2 : Slice Std.U32)
    (denominators flat : M31Vec) (line3Points : PointVec)
    (output : Output) : Prop :=
  SourceBatchInverseEvidence denominators (alloc.vec.Vec.deref flat) ∧
  SourceOutputEvidence layer0 line0 line1 line2 flat line3Points output

/-- A successful terminal iteration of the actual later-line source loop has
the proved batch-inverse and output-layout meaning.  In particular, the
source's first-entry check turns the arbitrary callback factor from the batch
wrapper into true inverses at every slot. -/
theorem source_terminal_success_exact
    (layer0 line0 line1 line2 : Slice Std.U32)
    (later : Array (Slice Std.U32) 3#usize)
    (inverseFn : M31 → M31) (line1Points line2Points line3Points : PointVec)
    (denominatorCount : Std.Usize) (denominators : M31Vec) (output : Output)
    (hlater0 : Array.index_usize later 0#usize = .ok line0)
    (hlater1 : Array.index_usize later 1#usize = .ok line1)
    (hlater2 : Array.index_usize later 2#usize = .ok line2)
    (hnonempty : 0 < denominators.val.length)
    (hdenominatorLength : denominators.val.length =
      2 * layer0.val.length + 3 * line0.val.length +
        3 * line1.val.length + 3 * line2.val.length)
    (hline3Points : ∀ ordinal, ordinal < line3Points.val.length →
      AspisV5FriCoordinateFieldSemantics.canonicalM31
        line3Points.val[ordinal]!.x)
    (hsuccess :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
          (sourcePointVecIterAt line1Points line2Points line3Points 3)
          layer0 later inverseFn line3Points denominatorCount denominators =
        .ok (.Ok output)) :
    ∃ flat : M31Vec,
      SourceTerminalEvidence layer0 line0 line1 line2 denominators flat
        line3Points output := by
  have hcountEq : alloc.vec.Vec.len denominators = denominatorCount := by
    by_contra hne
    have hterminal := hsuccess
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
      at hterminal
    rw [loop.eq_1] at hterminal
    simp only at hterminal
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0.body
      at hterminal
    rw [source_point_vec_next_three] at hterminal
    simp [massert, hne, Bind.bind, Aeneas.Std.bind] at hterminal
  have hcountAssert :
      massert (alloc.vec.Vec.len denominators = denominatorCount) = .ok () :=
    (massert_ok _).2 hcountEq
  obtain ⟨flatInitial, hflatInitialRun, hflatInitialValues,
    hflatInitialLength⟩ := Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.from_elem_spec
        V5CoordinateSelectedProductionSource.field.M31.Insts.CoreCloneClone
        V5CoordinateSelectedProductionSource.field.M31.ZERO
        (alloc.vec.Vec.len denominators) rfl)
  have hflatInitialCanonical :
      SourceCanonicalSlice (alloc.vec.Vec.deref flatInitial) := by
    intro index hindex
    change AspisV5FriCoordinateFieldSemantics.canonicalM31
      flatInitial.val[index]!
    change index < flatInitial.val.length at hindex
    rw [hflatInitialValues] at hindex ⊢
    rw [getElemBang_eq_getElem _ _ hindex]
    have hzero : AspisV5FriCoordinateFieldSemantics.canonicalM31
        V5CoordinateSelectedProductionSource.field.M31.ZERO := by
      norm_num [AspisV5FriCoordinateFieldSemantics.canonicalM31,
        AspisV5FriArithmeticSemantics.canonicalM31,
        AspisAeneasCM31Multiplicative.CanonicalRawM31,
        V5CoordinateSelectedProductionSource.field.M31.ZERO]
    simpa using hzero
  have hflatInitialLength' :
      (alloc.vec.Vec.deref flatInitial).val.length =
        denominators.val.length := by
    change flatInitial.val.length = denominators.val.length
    simpa using hflatInitialLength
  let initialSlice : Slice M31 :=
    (alloc.vec.Vec.deref_mut flatInitial).1
  have hinitialSliceLength : initialSlice.val.length =
      denominators.val.length := by
    change flatInitial.val.length = denominators.val.length
    exact hflatInitialLength'
  have hinitialSliceCanonical : SourceCanonicalSlice initialSlice := by
    intro index hindex
    apply hflatInitialCanonical index
    simpa [initialSlice, alloc.vec.Vec.deref_mut,
      alloc.vec.Vec.deref] using hindex
  obtain ⟨flatSlice, hbatchRun, hbatchPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (source_batch_inverse_wrapper_exact denominators
        initialSlice inverseFn hnonempty
        hinitialSliceLength hinitialSliceCanonical)
  rcases hbatchPost with ⟨backend, hbatchSuffix⟩
  let flat : M31Vec := (alloc.vec.Vec.deref_mut flatInitial).2 flatSlice
  have hbatchRun' :
      V5CoordinateSelectedProductionSource.field.m31_batch_inverse_with
          (alloc.vec.Vec.deref denominators)
          (alloc.vec.Vec.deref_mut flatInitial).1 inverseFn = .ok flatSlice := by
    simpa [initialSlice, alloc.vec.Vec.deref_mut,
      alloc.vec.Vec.deref] using hbatchRun
  have hflatBack :
      (alloc.vec.Vec.deref_mut flatInitial).2 flatSlice = flat := rfl
  have hflatLength : flat.val.length = denominators.val.length :=
    hbatchSuffix.1
  have hdenominatorsNotEmpty : denominators.val ≠ [] := by
    intro heq
    rw [heq] at hnonempty
    norm_num at hnonempty
  have hflatNotEmpty : flat.val ≠ [] := by
    intro heq
    have : flat.val.length = 0 := by simp [heq]
    rw [hflatLength] at this
    omega
  have hdenominatorsEmptyCall :
      alloc.vec.Vec.is_empty Global denominators = .ok false := by
    simp [alloc.vec.Vec.is_empty, hdenominatorsNotEmpty]
  have hflatEmptyCall : alloc.vec.Vec.is_empty Global flat = .ok false := by
    simp [alloc.vec.Vec.is_empty, hflatNotEmpty]
  obtain ⟨denominator0, hdenominator0Run, hdenominator0Value⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.index_usize_spec denominators 0#usize (by
        change 0 < denominators.val.length
        exact hnonempty))
  obtain ⟨inverse0, hinverse0Run, hinverse0Value⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.index_usize_spec flat 0#usize (by
        change 0 < flat.val.length
        rw [hflatLength]
        exact hnonempty))
  have hdenominator0Bang : denominator0 = denominators.val[0]! := by
    rw [hdenominator0Value]
    exact (getElemBang_eq_getElem denominators.val 0 hnonempty).symm
  have hinverse0Bang : inverse0 = flat.val[0]! := by
    rw [hinverse0Value]
    exact (getElemBang_eq_getElem flat.val 0
      (by rw [hflatLength]; exact hnonempty)).symm
  obtain ⟨check, hcheckRun, _hcheckCanonical, _hcheckValue⟩ :=
    source_mul_arbitrary_corresponds denominator0 inverse0
  have hcheckEq : check =
      V5CoordinateSelectedProductionSource.field.M31.ONE := by
    by_contra hne
    have hneRun :
        core.cmp.PartialEq.ne.trait_default
            V5CoordinateSelectedProductionSource.field.M31.Insts.CoreCmpPartialEqM31
            check V5CoordinateSelectedProductionSource.field.M31.ONE =
          .ok true := by
      simp [core.cmp.PartialEq.ne.trait_default,
        core.cmp.PartialEq.ne.default,
        V5CoordinateSelectedProductionSource.field.M31.Insts.CoreCmpPartialEqM31.eq,
        hne]
    have hbody :
        V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0.body
            layer0 later inverseFn line3Points denominatorCount
            (sourcePointVecIterAt line1Points line2Points line3Points 3)
            denominators =
          .ok (.done (.Err
            V5CoordinateSelectedProductionSource.circle_fri.CircleFriError.InvalidInverseBackend)) := by
      unfold
        V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0.body
      rw [source_point_vec_next_three]
      simp only [bind_tc_ok]
      rw [hcountAssert, hflatInitialRun]
      simp only [bind_tc_ok, Std.lift]
      rw [hbatchRun']
      simp only [bind_tc_ok]
      rw [hflatBack]
      rw [hdenominatorsEmptyCall, hflatEmptyCall]
      simp only [bind_tc_ok, Bool.false_eq_true, if_false]
      rw [alloc.vec.Vec.index_slice_index, hdenominator0Run,
        alloc.vec.Vec.index_slice_index, hinverse0Run]
      simp only [bind_tc_ok]
      rw [hcheckRun]
      simp only [bind_tc_ok]
      rw [hneRun]
      simp
    have hterminal := hsuccess
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
      at hterminal
    rw [loop.eq_1] at hterminal
    simp only at hterminal
    rw [hbody] at hterminal
    simp at hterminal
  have hsourceCheck :
      V5CoordinateSelectedProductionSource.field.M31.mul
          denominators.val[0]! flat.val[0]! =
        .ok V5CoordinateSelectedProductionSource.field.M31.ONE := by
    rw [← hdenominator0Bang, ← hinverse0Bang, hcheckRun, hcheckEq]
  have hbatchEvidence :
      SourceBatchInverseEvidence denominators (alloc.vec.Vec.deref flat) := by
    apply source_checked_batch_outputs_are_exact_inverses denominators
      (alloc.vec.Vec.deref flat) backend
    · simpa [flat, alloc.vec.Vec.deref, alloc.vec.Vec.deref_mut] using
        hbatchSuffix
    · exact hnonempty
    · exact hsourceCheck
  have hflatLayout : flat.val.length =
      2 * layer0.val.length + 3 * line0.val.length +
        3 * line1.val.length + 3 * line2.val.length := by
    rw [hflatLength, hdenominatorLength]
  obtain ⟨cursor0, circle, values0, values1, values2, cursor3, finalX,
    hcircleRun, hlaterRun, hcursor3, hfinalRun, houtputEvidence⟩ :=
      source_output_calls_exact layer0 line0 line1 line2 later flat
        line3Points hlater0 hlater1 hlater2 hflatLayout hline3Points
  have hcursorAssert :
      massert (cursor3 = alloc.vec.Vec.len flat) = .ok () := by
    apply (massert_ok _).2
    apply UScalar.eq_of_val_eq
    simpa using hcursor3
  have hneFalse :
      core.cmp.PartialEq.ne.trait_default
          V5CoordinateSelectedProductionSource.field.M31.Insts.CoreCmpPartialEqM31
          check V5CoordinateSelectedProductionSource.field.M31.ONE =
        .ok false := by
    subst check
    simp [core.cmp.PartialEq.ne.trait_default,
      core.cmp.PartialEq.ne.default,
      V5CoordinateSelectedProductionSource.field.M31.Insts.CoreCmpPartialEqM31.eq]
  have hcircleRun' := hcircleRun
  unfold sourceU32SliceIter at hcircleRun'
  have hfinalRun' := hfinalRun
  simp only [core.slice.Slice.iter, bind_tc_ok,
    core.iter.traits.iterator.Iterator.map.default] at hfinalRun'
  have hbody :
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0.body
          layer0 later inverseFn line3Points denominatorCount
          (sourcePointVecIterAt line1Points line2Points line3Points 3)
          denominators =
        .ok (.done (.Ok
          { circle := circle,
            later := Array.make 3#usize [values0, values1, values2],
            final_x := finalX })) := by
    unfold
      V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0.body
    rw [source_point_vec_next_three]
    simp only [bind_tc_ok]
    rw [hcountAssert, hflatInitialRun]
    simp only [bind_tc_ok, Std.lift]
    rw [hbatchRun']
    simp only [bind_tc_ok]
    rw [hflatBack]
    rw [hdenominatorsEmptyCall, hflatEmptyCall]
    simp only [bind_tc_ok, Bool.false_eq_true, if_false]
    rw [alloc.vec.Vec.index_slice_index, hdenominator0Run,
      alloc.vec.Vec.index_slice_index, hinverse0Run]
    simp only [bind_tc_ok]
    rw [hcheckRun]
    simp only [bind_tc_ok]
    rw [hneFalse]
    simp only [bind_tc_ok, Bool.false_eq_true, if_false,
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
    rw [hcircleRun']
    simp only [bind_tc_ok]
    rw [hlaterRun]
    simp only [bind_tc_ok]
    rw [hcursorAssert]
    simp only [bind_tc_ok, Std.lift,
      core.slice.Slice.iter,
      core.iter.traits.iterator.Iterator.map.default]
    rw [hfinalRun']
    rfl
  have hterminal := hsuccess
  unfold
    V5CoordinateSelectedProductionSource.circle_fri.derive_query_fold_inverses_for_circle_loop0_loop0
    at hterminal
  rw [loop.eq_1] at hterminal
  simp only at hterminal
  rw [hbody] at hterminal
  simp only at hterminal
  have houtputEq : output =
      { circle := circle,
        later := Array.make 3#usize [values0, values1, values2],
        final_x := finalX } := by
    exact core.result.Result.Ok.inj (Result.ok.inj hterminal).symm
  subst output
  exact ⟨flat, hbatchEvidence, houtputEvidence⟩


#print axioms source_mul_arbitrary_corresponds
#print axioms source_double_x_produces_canonical
#print axioms source_append_three_exact
#print axioms source_line_point_denominator_loop_exact
#print axioms source_three_line_outer_unroll
#print axioms source_three_line_outer_accepted
#print axioms source_pair_output_loop_exact
#print axioms source_triple_output_loop_exact
#print axioms source_triple_closure_call_exact
#print axioms source_later_from_fn_exact
#print axioms source_final_x_iter_to_list_exact
#print axioms source_final_x_collect_exact
#print axioms source_circle_prefix_loop_exact
#print axioms source_circle_prefix_from_empty_accepted
#print axioms source_terminal_success_exact

end V5CoordinateProductionTailProof
