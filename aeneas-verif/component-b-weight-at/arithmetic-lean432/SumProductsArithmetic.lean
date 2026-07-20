import AspisCoreQm31SumProductsSmall
import CM31MultiplicativeProof
import M31ReduceU64Proof

/-!
# Arithmetic support for the source-authentic small QM31 product sums

This file proves the generated nine-channel reconstruction function directly.
The loop proof is separate; no generic QM31 multiplication is used here.
-/

open Aeneas Aeneas.Std Result

namespace AspisLane5QM31SumProductsProof

abbrev RustM31 := AspisLane5QM31SumProductsSmall.field.M31
abbrev RustCM31 := AspisLane5QM31SumProductsSmall.field.CM31
abbrev RustQM31 := AspisLane5QM31SumProductsSmall.field.QM31

abbrev M31Exact := AspisAeneasCM31Exact.M31Exact
abbrev CM31Exact := AspisAeneasCM31Exact.CM31Exact
def qm31R : CM31Exact := ⟨2, 1⟩
abbrev QM31Exact := QuadraticAlgebra CM31Exact qm31R 0

abbrev m31Modulus : Nat := 2147483647
abbrev u64Cardinality : Nat := 2 ^ 64

abbrev CanonicalRawM31 :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31

def CanonicalCM31 (x : RustCM31) : Prop :=
  CanonicalRawM31 x.a.val ∧ CanonicalRawM31 x.b.val

def CanonicalQM31 (x : RustQM31) : Prop :=
  CanonicalCM31 x.c0 ∧ CanonicalCM31 x.c1

def cm31ToExact (x : RustCM31) : CM31Exact :=
  ⟨(x.a.val : M31Exact), (x.b.val : M31Exact)⟩

def qm31ToExact (x : RustQM31) : QM31Exact :=
  ⟨cm31ToExact x.c0, cm31ToExact x.c1⟩

private theorem P_eq_existing :
    AspisLane5QM31SumProductsSmall.field.P =
      AspisCoreCM31Multiplicative.field.P := by
  apply UScalar.eq_of_val_eq
  unfold AspisLane5QM31SumProductsSmall.field.P
    AspisCoreCM31Multiplicative.field.P
  rfl

private theorem P_eq_reduce_existing :
    AspisLane5QM31SumProductsSmall.field.P = aspis_core.field.P := by
  apply UScalar.eq_of_val_eq
  unfold AspisLane5QM31SumProductsSmall.field.P aspis_core.field.P
  rfl

private theorem m31_add_eq_existing (a b : RustM31) :
    AspisLane5QM31SumProductsSmall.field.M31.add a b =
      AspisCoreCM31Multiplicative.field.M31.add a b := by
  unfold AspisLane5QM31SumProductsSmall.field.M31.add
    AspisCoreCM31Multiplicative.field.M31.add
  rw [P_eq_existing]

private theorem m31_sub_eq_existing (a b : RustM31) :
    AspisLane5QM31SumProductsSmall.field.M31.sub a b =
      AspisCoreCM31Multiplicative.field.M31.sub a b := by
  unfold AspisLane5QM31SumProductsSmall.field.M31.sub
    AspisCoreCM31Multiplicative.field.M31.sub
  rw [P_eq_existing]

private theorem reduce_u64_eq_existing (x : Std.U64) :
    AspisLane5QM31SumProductsSmall.field.reduce_u64 x =
      aspis_core.field.reduce_u64 x := by
  unfold AspisLane5QM31SumProductsSmall.field.reduce_u64
    aspis_core.field.reduce_u64
  rw [P_eq_reduce_existing]

private theorem m31_add_corresponds
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : RustM31,
      AspisLane5QM31SumProductsSmall.field.M31.add a b = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) + (b.val : M31Exact) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      a b ha hb with ⟨out, hout, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  rw [m31_add_eq_existing]
  exact hout

private theorem m31_sub_corresponds
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : RustM31,
      AspisLane5QM31SumProductsSmall.field.M31.sub a b = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) - (b.val : M31Exact) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      a b ha hb with ⟨out, hout, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  rw [m31_sub_eq_existing]
  exact hout

private theorem m31_double_corresponds
    (a : RustM31) (ha : CanonicalRawM31 a.val) :
    ∃ out : RustM31,
      AspisLane5QM31SumProductsSmall.field.M31.double a = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) + (a.val : M31Exact) := by
  rcases m31_add_corresponds a a ha ha with
    ⟨out, hout, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  simpa [AspisLane5QM31SumProductsSmall.field.M31.double] using hout

private theorem m31_reduce_u64_corresponds (x : Std.U64) :
    ∃ out : RustM31,
      AspisLane5QM31SumProductsSmall.field.M31.reduce_u64 x = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) = (x.val : M31Exact) := by
  rcases AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds x with
    ⟨out, hout, _hraw, hcanonical, hexact⟩
  have hfresh :
      AspisLane5QM31SumProductsSmall.field.reduce_u64 x = ok out := by
    rw [reduce_u64_eq_existing]
    exact hout
  refine ⟨out, ?_, hcanonical, hexact⟩
  simp [AspisLane5QM31SumProductsSmall.field.M31.reduce_u64, hfresh]

private theorem cm31_add_corresponds
    (x y : RustCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : RustCM31,
      AspisLane5QM31SumProductsSmall.field.CM31.add x y = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = cm31ToExact x + cm31ToExact y := by
  rcases m31_add_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases m31_add_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [AspisLane5QM31SumProductsSmall.field.CM31.add,
      hcallA, hcallB]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

private theorem cm31_sub_corresponds
    (x y : RustCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : RustCM31,
      AspisLane5QM31SumProductsSmall.field.CM31.sub x y = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = cm31ToExact x - cm31ToExact y := by
  rcases m31_sub_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases m31_sub_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [AspisLane5QM31SumProductsSmall.field.CM31.sub,
      hcallA, hcallB]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

private theorem mul_by_r_corresponds
    (x : RustCM31) (hx : CanonicalCM31 x) :
    ∃ out : RustCM31,
      AspisLane5QM31SumProductsSmall.field.mul_by_r x = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = qm31R * cm31ToExact x := by
  rcases m31_double_corresponds x.a hx.1 with
    ⟨doubleA, hdoubleA, hdoubleACan, hdoubleAExact⟩
  rcases m31_sub_corresponds doubleA x.b hdoubleACan hx.2 with
    ⟨real, hreal, hrealCan, hrealExact⟩
  rcases m31_double_corresponds x.b hx.2 with
    ⟨doubleB, hdoubleB, hdoubleBCan, hdoubleBExact⟩
  rcases m31_add_corresponds x.a doubleB hx.1 hdoubleBCan with
    ⟨imag, himag, himagCan, himagExact⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCan, himagCan⟩, ?_⟩
  · simp [AspisLane5QM31SumProductsSmall.field.mul_by_r,
      hdoubleA, hreal, hdoubleB, himag]
  · apply QuadraticAlgebra.ext
    · simp [cm31ToExact, qm31R, hrealExact, hdoubleAExact]
      ring
    · simp [cm31ToExact, qm31R, himagExact, hdoubleBExact]
      ring

private theorem list_get_eq_getElemBang
    {T : Type} [Inhabited T]
    (values : List T) (index : Nat) (hIndex : index < values.length) :
    values[index] = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [hIndex]

private theorem generated_array_index_run
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hIndex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, hRun, hValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hIndex))
  have hArrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hIndex
  have hElem := list_get_eq_getElemBang values.val index.val hArrayBound
  simpa [hValue, hElem] using hRun

private theorem generated_array_index_exists
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hIndex : index.val < N.val) :
    ∃ value : T,
      Array.index_usize values index = ok value ∧
      value = values.val[index.val]! := by
  obtain ⟨value, hRun, hValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hIndex))
  have hArrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hIndex
  have hElem := list_get_eq_getElemBang values.val index.val hArrayBound
  exact ⟨value, hRun, hValue.trans hElem⟩

def rowCell (row : Array Std.U64 3#usize) (channel : Nat) : Std.U64 :=
  row.val[channel]!

def matrixCell
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (component channel : Nat) : Std.U64 :=
  rowCell sums.val[component]! channel

def reconstructCMExact (row : Array Std.U64 3#usize) : CM31Exact :=
  ⟨((rowCell row 0).val : M31Exact) -
      ((rowCell row 1).val : M31Exact),
    ((rowCell row 2).val : M31Exact) -
      ((rowCell row 0).val : M31Exact) -
      ((rowCell row 1).val : M31Exact)⟩

def reconstructQMExact
    (sums : Array (Array Std.U64 3#usize) 3#usize) : QM31Exact :=
  let m0 := reconstructCMExact sums.val[(0#usize).val]!
  let m1 := reconstructCMExact sums.val[(1#usize).val]!
  let m2 := reconstructCMExact sums.val[(2#usize).val]!
  ⟨m0 + qm31R * m1, m2 - m0 - m1⟩

private theorem extracted_reconstruct_closure_corresponds
    (channels : Array Std.U64 3#usize) :
    ∃ out : RustCM31,
      AspisLane5QM31SumProductsSmall.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
          () channels = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = reconstructCMExact channels := by
  have h0 := generated_array_index_run channels 0#usize (by norm_num)
  have h1 := generated_array_index_run channels 1#usize (by norm_num)
  have h2 := generated_array_index_run channels 2#usize (by norm_num)
  have hget0 : channels.val[0] = rowCell channels 0 := by
    exact list_get_eq_getElemBang channels.val 0 (by simp)
  have hget1 : channels.val[1] = rowCell channels 1 := by
    exact list_get_eq_getElemBang channels.val 1 (by simp)
  have hget2 : channels.val[2] = rowCell channels 2 := by
    exact list_get_eq_getElemBang channels.val 2 (by simp)
  rcases m31_reduce_u64_corresponds (rowCell channels 0) with
    ⟨m0, hm0, hm0Can, hm0Exact⟩
  rcases m31_reduce_u64_corresponds (rowCell channels 1) with
    ⟨m1, hm1, hm1Can, hm1Exact⟩
  rcases m31_reduce_u64_corresponds (rowCell channels 2) with
    ⟨m2, hm2, hm2Can, hm2Exact⟩
  rcases m31_sub_corresponds m0 m1 hm0Can hm1Can with
    ⟨real, hreal, hrealCan, hrealExact⟩
  rcases m31_sub_corresponds m2 m0 hm2Can hm0Can with
    ⟨imag0, himag0, himag0Can, himag0Exact⟩
  rcases m31_sub_corresponds imag0 m1 himag0Can hm1Can with
    ⟨imag, himag, himagCan, himagExact⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCan, himagCan⟩, ?_⟩
  · simp [AspisLane5QM31SumProductsSmall.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call,
      h0, h1, h2, hget0, hget1, hget2,
      hm0, hm1, hm2, hreal, himag0, himag]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : M31Exact) =
        ((rowCell channels 0).val : M31Exact) -
          ((rowCell channels 1).val : M31Exact)
      rw [hrealExact, hm0Exact, hm1Exact]
    · calc
        (cm31ToExact ⟨real, imag⟩).im =
            ((imag.val : Nat) : M31Exact) := rfl
        _ = ((imag0.val : Nat) : M31Exact) -
              ((m1.val : Nat) : M31Exact) := himagExact
        _ = (((m2.val : Nat) : M31Exact) -
              ((m0.val : Nat) : M31Exact)) -
              ((m1.val : Nat) : M31Exact) := by rw [himag0Exact]
        _ = (reconstructCMExact channels).im := by
          change _ = ((rowCell channels 2).val : M31Exact) -
            ((rowCell channels 0).val : M31Exact) -
            ((rowCell channels 1).val : M31Exact)
          rw [hm0Exact, hm1Exact, hm2Exact]

/-- Direct correspondence for the generated nine-channel reconstruction.
It performs each of the nine generated reductions and the generated
CM31/QM31 Karatsuba reconstruction. -/
theorem extracted_qm31_from_karatsuba_channel_sums_corresponds
    (sums : Array (Array Std.U64 3#usize) 3#usize) :
    ∃ out : RustQM31,
      AspisLane5QM31SumProductsSmall.field.qm31_from_karatsuba_channel_sums
          sums = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = reconstructQMExact sums := by
  rcases generated_array_index_exists sums 0#usize (by norm_num) with
    ⟨row0, hrow0, hrow0Val⟩
  rcases generated_array_index_exists sums 1#usize (by norm_num) with
    ⟨row1, hrow1, hrow1Val⟩
  rcases generated_array_index_exists sums 2#usize (by norm_num) with
    ⟨row2, hrow2, hrow2Val⟩
  rcases extracted_reconstruct_closure_corresponds row0 with
    ⟨m0, hm0, hm0Can, hm0Exact⟩
  rcases extracted_reconstruct_closure_corresponds row1 with
    ⟨m1, hm1, hm1Can, hm1Exact⟩
  rcases extracted_reconstruct_closure_corresponds row2 with
    ⟨m2, hm2, hm2Can, hm2Exact⟩
  rcases mul_by_r_corresponds m1 hm1Can with
    ⟨rm1, hrm1, hrm1Can, hrm1Exact⟩
  rcases cm31_add_corresponds m0 rm1 hm0Can hrm1Can with
    ⟨low, hlow, hlowCan, hlowExact⟩
  rcases cm31_sub_corresponds m2 m0 hm2Can hm0Can with
    ⟨high0, hhigh0, hhigh0Can, hhigh0Exact⟩
  rcases cm31_sub_corresponds high0 m1 hhigh0Can hm1Can with
    ⟨high, hhigh, hhighCan, hhighExact⟩
  refine ⟨⟨low, high⟩, ?_, ⟨hlowCan, hhighCan⟩, ?_⟩
  · unfold AspisLane5QM31SumProductsSmall.field.qm31_from_karatsuba_channel_sums
    rw [hrow0]
    simp only [bind_tc_ok]
    rw [hm0]
    simp only [bind_tc_ok]
    rw [hrow1]
    simp only [bind_tc_ok]
    rw [hm1]
    simp only [bind_tc_ok]
    rw [hrow2]
    simp only [bind_tc_ok]
    rw [hm2]
    simp only [bind_tc_ok]
    rw [hrm1]
    simp only [bind_tc_ok]
    rw [hlow]
    simp only [bind_tc_ok]
    rw [hhigh0]
    simp only [bind_tc_ok]
    rw [hhigh]
    simp only [bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · calc
        (qm31ToExact ⟨low, high⟩).re = cm31ToExact low := rfl
        _ = cm31ToExact m0 + cm31ToExact rm1 := hlowExact
        _ = cm31ToExact m0 + qm31R * cm31ToExact m1 := by rw [hrm1Exact]
        _ = (reconstructQMExact sums).re := by
          change _ = reconstructCMExact sums.val[(0#usize).val]! +
            qm31R * reconstructCMExact sums.val[(1#usize).val]!
          rw [hm0Exact, hm1Exact, hrow0Val, hrow1Val]
    · calc
        (qm31ToExact ⟨low, high⟩).im = cm31ToExact high := rfl
        _ = cm31ToExact high0 - cm31ToExact m1 := hhighExact
        _ = (cm31ToExact m2 - cm31ToExact m0) - cm31ToExact m1 := by
          rw [hhigh0Exact]
        _ = (reconstructQMExact sums).im := by
          change _ = reconstructCMExact sums.val[(2#usize).val]! -
            reconstructCMExact sums.val[(0#usize).val]! -
            reconstructCMExact sums.val[(1#usize).val]!
          rw [hm0Exact, hm1Exact, hm2Exact, hrow0Val, hrow1Val, hrow2Val]

/-! A concrete tooth for the non-residue sign used by reconstruction. -/

def reconstructQMExactWrongR
    (sums : Array (Array Std.U64 3#usize) 3#usize) : QM31Exact :=
  let m0 := reconstructCMExact sums.val[(0#usize).val]!
  let m1 := reconstructCMExact sums.val[(1#usize).val]!
  let m2 := reconstructCMExact sums.val[(2#usize).val]!
  ⟨m0 + (⟨2, -1⟩ : CM31Exact) * m1, m2 - m0 - m1⟩

def rSignToothSums : Array (Array Std.U64 3#usize) 3#usize :=
  Array.make 3#usize [
    Array.make 3#usize [0#u64, 0#u64, 0#u64],
    Array.make 3#usize [1#u64, 0#u64, 1#u64],
    Array.make 3#usize [0#u64, 0#u64, 0#u64]
  ]

theorem reconstruct_with_two_minus_i_is_wrong :
    reconstructQMExactWrongR rSignToothSums ≠
      reconstructQMExact rSignToothSums := by
  intro h
  have hcoord := congrArg (fun z : QM31Exact => z.re.im) h
  norm_num [reconstructQMExactWrongR, reconstructQMExact,
    reconstructCMExact, rowCell, rSignToothSums, qm31R] at hcoord
  change (-1 : M31Exact) = 1 at hcoord
  exact (by decide : (-1 : M31Exact) ≠ 1) hcoord

#print axioms extracted_qm31_from_karatsuba_channel_sums_corresponds
#print axioms reconstruct_with_two_minus_i_is_wrong

end AspisLane5QM31SumProductsProof
