import V5RelationKernels
import QM31MulProof
import QM31SquareScalarsProof
import AspisFormal.V5PreparedPointClaimsSourceBridge

/-!
# Extracted V5 prepared-point-claim kernels

This file proves the production gamma-power and bounded dot-product helpers
extracted by Charon and Aeneas.  The byte-decoder proof is compiled separately
because the two generated extraction packages use conflicting global names.
The enclosing `prepare_v5_pcs_claims` function is not translated by the pinned
Aeneas version: its nested loops contain early returns.  The exact remaining
connection is therefore the small source-shaped outer driver that calls these
proved kernels in the production order.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5PreparedPointClaimsSourceProof

open AspisV5ComponentCQM31Representation
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCPreProjectionDeployed
open AspisV5PreparedPointClaimsSourceBridge

/-! ## Arithmetic used by the two extracted kernels

The fixed-loop proofs below use the exact quadratic tower already established
for the production field implementation.  These adapters are small because an
M31 value is the same `u32` in both extraction packages; only the generated
CM31 and QM31 structure names differ.
-/

abbrev KernelM31 :=
  V5RelationPreparedClaimsGenerated.aspis_core.field.M31
abbrev KernelCM31 :=
  V5RelationPreparedClaimsGenerated.aspis_core.field.CM31
abbrev KernelQM31 :=
  V5RelationPreparedClaimsGenerated.aspis_core.field.QM31
abbrev KernelM31Exact := AspisAeneasQM31Mul.M31Exact
abbrev KernelCM31Exact := AspisAeneasQM31Mul.CM31Exact
abbrev KernelQM31Exact := AspisAeneasQM31Mul.QM31Exact

def kernelCM31ToExact (x : KernelCM31) : KernelCM31Exact :=
  ⟨(x.a.val : KernelM31Exact), (x.b.val : KernelM31Exact)⟩

def kernelQM31ToExact (x : KernelQM31) : KernelQM31Exact :=
  ⟨kernelCM31ToExact x.c0, kernelCM31ToExact x.c1⟩

abbrev KernelCanonicalM31 :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31

def KernelCanonicalCM31 (x : KernelCM31) : Prop :=
  KernelCanonicalM31 x.a.val ∧ KernelCanonicalM31 x.b.val

def KernelCanonicalQM31 (x : KernelQM31) : Prop :=
  KernelCanonicalCM31 x.c0 ∧ KernelCanonicalCM31 x.c1

private theorem kernel_P_eq_existing :
    V5RelationPreparedClaimsGenerated.aspis_core.field.P =
      AspisCoreCM31Multiplicative.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5RelationPreparedClaimsGenerated.aspis_core.field.P
    AspisCoreCM31Multiplicative.field.P
  rfl

private theorem kernel_reduce_u64_eq_existing (x : Std.U64) :
    V5RelationPreparedClaimsGenerated.aspis_core.field.reduce_u64 x =
      AspisCoreCM31Multiplicative.field.reduce_u64 x := by
  unfold V5RelationPreparedClaimsGenerated.aspis_core.field.reduce_u64
    AspisCoreCM31Multiplicative.field.reduce_u64
  rw [kernel_P_eq_existing]

private theorem kernel_m31_add_eq_existing (x y : KernelM31) :
    V5RelationPreparedClaimsGenerated.aspis_core.field.M31.add x y =
      AspisCoreCM31Multiplicative.field.M31.add x y := by
  unfold V5RelationPreparedClaimsGenerated.aspis_core.field.M31.add
    AspisCoreCM31Multiplicative.field.M31.add
  rw [kernel_P_eq_existing]

private theorem kernel_m31_sub_eq_existing (x y : KernelM31) :
    V5RelationPreparedClaimsGenerated.aspis_core.field.M31.sub x y =
      AspisCoreCM31Multiplicative.field.M31.sub x y := by
  unfold V5RelationPreparedClaimsGenerated.aspis_core.field.M31.sub
    AspisCoreCM31Multiplicative.field.M31.sub
  rw [kernel_P_eq_existing]

private theorem kernel_m31_mul_eq_existing (x y : KernelM31) :
    V5RelationPreparedClaimsGenerated.aspis_core.field.M31.mul x y =
      AspisCoreCM31Multiplicative.field.M31.mul x y := by
  unfold V5RelationPreparedClaimsGenerated.aspis_core.field.M31.mul
    AspisCoreCM31Multiplicative.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [kernel_reduce_u64_eq_existing]

private theorem kernel_m31_add_corresponds
    (x y : KernelM31) (hx : KernelCanonicalM31 x.val)
    (hy : KernelCanonicalM31 y.val) :
    ∃ out : KernelM31,
      V5RelationPreparedClaimsGenerated.aspis_core.field.M31.add x y =
        .ok out ∧
      KernelCanonicalM31 out.val ∧
      ((out.val : Nat) : KernelM31Exact) =
        (x.val : KernelM31Exact) + (y.val : KernelM31Exact) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      x y hx hy with ⟨out, hout, hcanonical, hexact⟩
  exact ⟨out, kernel_m31_add_eq_existing x y |>.trans hout,
    hcanonical, hexact⟩

private theorem kernel_m31_sub_corresponds
    (x y : KernelM31) (hx : KernelCanonicalM31 x.val)
    (hy : KernelCanonicalM31 y.val) :
    ∃ out : KernelM31,
      V5RelationPreparedClaimsGenerated.aspis_core.field.M31.sub x y =
        .ok out ∧
      KernelCanonicalM31 out.val ∧
      ((out.val : Nat) : KernelM31Exact) =
        (x.val : KernelM31Exact) - (y.val : KernelM31Exact) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      x y hx hy with ⟨out, hout, hcanonical, hexact⟩
  exact ⟨out, kernel_m31_sub_eq_existing x y |>.trans hout,
    hcanonical, hexact⟩

private theorem kernel_m31_mul_corresponds
    (x y : KernelM31) (hx : KernelCanonicalM31 x.val)
    (hy : KernelCanonicalM31 y.val) :
    ∃ out : KernelM31,
      V5RelationPreparedClaimsGenerated.aspis_core.field.M31.mul x y =
        .ok out ∧
      KernelCanonicalM31 out.val ∧
      ((out.val : Nat) : KernelM31Exact) =
        (x.val : KernelM31Exact) * (y.val : KernelM31Exact) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds
      x y hx hy with ⟨out, hout, hcanonical, hexact⟩
  exact ⟨out, kernel_m31_mul_eq_existing x y |>.trans hout,
    hcanonical, hexact⟩

private theorem kernel_m31_double_corresponds
    (x : KernelM31) (hx : KernelCanonicalM31 x.val) :
    ∃ out : KernelM31,
      V5RelationPreparedClaimsGenerated.aspis_core.field.M31.double x =
        .ok out ∧
      KernelCanonicalM31 out.val ∧
      ((out.val : Nat) : KernelM31Exact) =
        (x.val : KernelM31Exact) + (x.val : KernelM31Exact) := by
  rcases kernel_m31_add_corresponds x x hx hx with
    ⟨out, hout, hcanonical, hexact⟩
  exact ⟨out, by simpa [V5RelationPreparedClaimsGenerated.aspis_core.field.M31.double]
    using hout, hcanonical, hexact⟩

private theorem kernel_cm31_add_corresponds
    (x y : KernelCM31) (hx : KernelCanonicalCM31 x)
    (hy : KernelCanonicalCM31 y) :
    ∃ out : KernelCM31,
      V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.add x y =
        .ok out ∧
      KernelCanonicalCM31 out ∧
      kernelCM31ToExact out =
        kernelCM31ToExact x + kernelCM31ToExact y := by
  rcases kernel_m31_add_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, hoa, hca, hea⟩
  rcases kernel_m31_add_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hob, hcb, heb⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hca, hcb⟩, ?_⟩
  · simp [V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.add,
      hoa, hob]
  · apply QuadraticAlgebra.ext <;> assumption

private theorem kernel_cm31_sub_corresponds
    (x y : KernelCM31) (hx : KernelCanonicalCM31 x)
    (hy : KernelCanonicalCM31 y) :
    ∃ out : KernelCM31,
      V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.sub x y =
        .ok out ∧
      KernelCanonicalCM31 out ∧
      kernelCM31ToExact out =
        kernelCM31ToExact x - kernelCM31ToExact y := by
  rcases kernel_m31_sub_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, hoa, hca, hea⟩
  rcases kernel_m31_sub_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hob, hcb, heb⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hca, hcb⟩, ?_⟩
  · simp [V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.sub,
      hoa, hob]
  · apply QuadraticAlgebra.ext <;> assumption

private theorem kernel_cm31_mul_corresponds
    (x y : KernelCM31) (hx : KernelCanonicalCM31 x)
    (hy : KernelCanonicalCM31 y) :
    ∃ out : KernelCM31,
      V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.mul x y =
        .ok out ∧
      KernelCanonicalCM31 out ∧
      kernelCM31ToExact out =
        kernelCM31ToExact x * kernelCM31ToExact y := by
  rcases kernel_m31_mul_corresponds x.a y.a hx.1 hy.1 with
    ⟨m0, hm0, hcm0, hem0⟩
  rcases kernel_m31_mul_corresponds x.b y.b hx.2 hy.2 with
    ⟨m1, hm1, hcm1, hem1⟩
  rcases kernel_m31_add_corresponds x.a x.b hx.1 hx.2 with
    ⟨xs, hxs, hcxs, hexs⟩
  rcases kernel_m31_add_corresponds y.a y.b hy.1 hy.2 with
    ⟨ys, hys, hcys, heys⟩
  rcases kernel_m31_mul_corresponds xs ys hcxs hcys with
    ⟨m2, hm2, hcm2, hem2⟩
  rcases kernel_m31_sub_corresponds m0 m1 hcm0 hcm1 with
    ⟨real, hreal, hcreal, hereal⟩
  rcases kernel_m31_sub_corresponds m2 m0 hcm2 hcm0 with
    ⟨imag0, himag0, hcimag0, heimag0⟩
  rcases kernel_m31_sub_corresponds imag0 m1 hcimag0 hcm1 with
    ⟨imag, himag, hcimag, heimag⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hcreal, hcimag⟩, ?_⟩
  · simp [V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.mul,
      hm0, hm1, hxs, hys, hm2, hreal, himag0, himag]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : KernelM31Exact) = _
      rw [hereal, hem0, hem1]
      simp only [kernelCM31ToExact, QuadraticAlgebra.re_mul]
      ring
    · change ((imag.val : Nat) : KernelM31Exact) = _
      rw [heimag, heimag0, hem2, hem0, hem1, hexs, heys]
      simp only [kernelCM31ToExact, QuadraticAlgebra.im_mul]
      ring

private theorem kernel_cm31_square_corresponds
    (x : KernelCM31) (hx : KernelCanonicalCM31 x) :
    ∃ out : KernelCM31,
      V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.square x =
        .ok out ∧
      KernelCanonicalCM31 out ∧
      kernelCM31ToExact out = kernelCM31ToExact x * kernelCM31ToExact x := by
  rcases kernel_m31_add_corresponds x.a x.b hx.1 hx.2 with
    ⟨sum, hsum, hcsum, hesum⟩
  rcases kernel_m31_sub_corresponds x.a x.b hx.1 hx.2 with
    ⟨diff, hdiff, hcdiff, hediff⟩
  rcases kernel_m31_mul_corresponds sum diff hcsum hcdiff with
    ⟨real, hreal, hcreal, hereal⟩
  rcases kernel_m31_mul_corresponds x.a x.b hx.1 hx.2 with
    ⟨ab, hab, hcab, heab⟩
  rcases kernel_m31_double_corresponds ab hcab with
    ⟨imag, himag, hcimag, heimag⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hcreal, hcimag⟩, ?_⟩
  · simp [V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.square,
      hsum, hdiff, hreal, hab, himag]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : KernelM31Exact) = _
      rw [hereal, hesum, hediff]
      simp only [kernelCM31ToExact, QuadraticAlgebra.re_mul]
      ring
    · change ((imag.val : Nat) : KernelM31Exact) = _
      rw [heimag, heab]
      simp only [kernelCM31ToExact, QuadraticAlgebra.im_mul]
      ring

private theorem kernel_mul_by_r_corresponds
    (x : KernelCM31) (hx : KernelCanonicalCM31 x) :
    ∃ out : KernelCM31,
      V5RelationPreparedClaimsGenerated.aspis_core.field.mul_by_r x =
        .ok out ∧
      KernelCanonicalCM31 out ∧
      kernelCM31ToExact out =
        kernelCM31ToExact x * AspisAeneasQM31Mul.qm31R := by
  rcases kernel_m31_double_corresponds x.a hx.1 with
    ⟨twoA, htwoA, hctwoA, hetwoA⟩
  rcases kernel_m31_sub_corresponds twoA x.b hctwoA hx.2 with
    ⟨real, hreal, hcreal, hereal⟩
  rcases kernel_m31_double_corresponds x.b hx.2 with
    ⟨twoB, htwoB, hctwoB, hetwoB⟩
  rcases kernel_m31_add_corresponds x.a twoB hx.1 hctwoB with
    ⟨imag, himag, hcimag, heimag⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hcreal, hcimag⟩, ?_⟩
  · simp [V5RelationPreparedClaimsGenerated.aspis_core.field.mul_by_r,
      htwoA, hreal, htwoB, himag]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : KernelM31Exact) = _
      rw [hereal, hetwoA]
      simp only [kernelCM31ToExact, AspisAeneasQM31Mul.qm31R,
        QuadraticAlgebra.re_mul]
      ring
    · change ((imag.val : Nat) : KernelM31Exact) = _
      rw [heimag, hetwoB]
      simp only [kernelCM31ToExact, AspisAeneasQM31Mul.qm31R,
        QuadraticAlgebra.im_mul]
      ring

/-- The multiplication called by the extracted kernels is the exact QM31
multiplication for every canonical pair. -/
theorem extracted_kernel_qm31_mul_corresponds
    (x y : KernelQM31) (hx : KernelCanonicalQM31 x)
    (hy : KernelCanonicalQM31 y) :
    ∃ out : KernelQM31,
      V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.mul x y =
        .ok out ∧
      KernelCanonicalQM31 out ∧
      kernelQM31ToExact out =
        kernelQM31ToExact x * kernelQM31ToExact y := by
  rcases kernel_cm31_mul_corresponds x.c0 y.c0 hx.1 hy.1 with
    ⟨m0, hm0, hcm0, hem0⟩
  rcases kernel_cm31_mul_corresponds x.c1 y.c1 hx.2 hy.2 with
    ⟨m1, hm1, hcm1, hem1⟩
  rcases kernel_cm31_add_corresponds x.c0 x.c1 hx.1 hx.2 with
    ⟨xs, hxs, hcxs, hexs⟩
  rcases kernel_cm31_add_corresponds y.c0 y.c1 hy.1 hy.2 with
    ⟨ys, hys, hcys, heys⟩
  rcases kernel_cm31_mul_corresponds xs ys hcxs hcys with
    ⟨m2, hm2, hcm2, hem2⟩
  rcases kernel_mul_by_r_corresponds m1 hcm1 with
    ⟨rm1, hrm1, hcrm1, herm1⟩
  rcases kernel_cm31_add_corresponds m0 rm1 hcm0 hcrm1 with
    ⟨low, hlow, hclow, helow⟩
  rcases kernel_cm31_sub_corresponds m2 m0 hcm2 hcm0 with
    ⟨high0, hhigh0, hchigh0, hehigh0⟩
  rcases kernel_cm31_sub_corresponds high0 m1 hchigh0 hcm1 with
    ⟨high, hhigh, hchigh, hehigh⟩
  refine ⟨⟨low, high⟩, ?_, ⟨hclow, hchigh⟩, ?_⟩
  · simp [V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.mul,
      hm0, hm1, hxs, hys, hm2, hrm1, hlow, hhigh0, hhigh]
  · apply QuadraticAlgebra.ext
    · change kernelCM31ToExact low = _
      rw [helow, hem0, herm1, hem1]
      simp only [kernelQM31ToExact, QuadraticAlgebra.re_mul]
      ring
    · change kernelCM31ToExact high = _
      rw [hehigh, hehigh0, hem2, hem0, hem1, hexs, heys]
      simp only [kernelQM31ToExact, QuadraticAlgebra.im_mul]
      ring

/-- The optimized square called by the extracted gamma builder is exact for
every canonical input. -/
theorem extracted_kernel_qm31_square_corresponds
    (x : KernelQM31) (hx : KernelCanonicalQM31 x) :
    ∃ out : KernelQM31,
      V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.square x =
        .ok out ∧
      KernelCanonicalQM31 out ∧
      kernelQM31ToExact out = kernelQM31ToExact x * kernelQM31ToExact x := by
  rcases kernel_cm31_square_corresponds x.c0 hx.1 with
    ⟨c0sq, hc0sq, hcc0sq, hec0sq⟩
  rcases kernel_cm31_square_corresponds x.c1 hx.2 with
    ⟨c1sq, hc1sq, hcc1sq, hec1sq⟩
  rcases kernel_mul_by_r_corresponds c1sq hcc1sq with
    ⟨rc1sq, hrc1sq, hcrc1sq, herc1sq⟩
  rcases kernel_cm31_add_corresponds c0sq rc1sq hcc0sq hcrc1sq with
    ⟨low, hlow, hclow, helow⟩
  rcases kernel_cm31_mul_corresponds x.c0 x.c1 hx.1 hx.2 with
    ⟨cross, hcross, hccross, hecross⟩
  rcases kernel_cm31_add_corresponds cross cross hccross hccross with
    ⟨high, hhigh, hchigh, hehigh⟩
  refine ⟨⟨low, high⟩, ?_, ⟨hclow, hchigh⟩, ?_⟩
  · simp [V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.square,
      V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.double,
      hc0sq, hc1sq, hrc1sq, hlow, hcross, hhigh]
  · apply QuadraticAlgebra.ext
    · change kernelCM31ToExact low = _
      rw [helow, hec0sq, herc1sq, hec1sq]
      simp only [kernelQM31ToExact, QuadraticAlgebra.re_mul]
      ring
    · change kernelCM31ToExact high = _
      rw [hehigh, hecross]
      simp only [kernelQM31ToExact, QuadraticAlgebra.im_mul]
      ring

/-! ## Exact extracted gamma-power loop -/

private instance kernelQM31Inhabited : Inhabited KernelQM31 :=
  ⟨V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ZERO⟩

def kernelArrayEntry {N : Std.Usize} (values : Array KernelQM31 N)
    (index : Fin N.val) : KernelQM31 :=
  values.val[index.val]!

private theorem kernel_array_index_call {N : Std.Usize}
    (values : Array KernelQM31 N) (index : Std.Usize)
    (hindex : index.val < N.val) :
    Array.index_usize values index =
      .ok (kernelArrayEntry values ⟨index.val, hindex⟩) := by
  obtain ⟨value, hrun, hvalue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have harrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have hbang : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    exact List.getElem?_eq_getElem harrayBound
  simpa [kernelArrayEntry, hvalue, hbang] using hrun

private theorem kernel_array_update_call {N : Std.Usize}
    (values : Array KernelQM31 N) (index : Std.Usize)
    (hindex : index.val < N.val) (value : KernelQM31) :
    Array.update values index value = .ok (values.set index value) := by
  unfold Array.update
  rw [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem (by rw [values.property]; exact hindex)]
  apply congrArg Result.ok
  apply Subtype.ext
  rfl

@[simp] private theorem kernel_array_entry_set_self {N : Std.Usize}
    (values : Array KernelQM31 N) (index : Std.Usize)
    (hindex : index.val < N.val) (value : KernelQM31) :
    kernelArrayEntry (values.set index value) ⟨index.val, hindex⟩ = value := by
  unfold kernelArrayEntry
  simp only [Array.set_val_eq]
  apply List.set_getElem!_eq
  exact ⟨by rw [values.property]; exact hindex, rfl⟩

@[simp] private theorem kernel_array_entry_set_other {N : Std.Usize}
    (values : Array KernelQM31 N) (index : Std.Usize)
    (value : KernelQM31) (output : Fin N.val)
    (hne : index.val ≠ output.val) :
    kernelArrayEntry (values.set index value) output =
      kernelArrayEntry values output := by
  unfold kernelArrayEntry
  simp only [Array.set_val_eq]
  exact List.set_getElem!_ne values.val index.val output.val value
    (Or.inl hne)

private theorem kernel_usize_wrapping_add_one_val (index : Std.Usize)
    (hbound : index.val < 19) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hone : (1#usize : Std.Usize).val = 1 := rfl
  rw [hone]
  have room : 20 < UScalar.size .Usize := by
    have h := (20#usize).hSize
    scalar_tac
  omega

private theorem kernel_usize_wrapping_sub_one_val (index : Std.Usize)
    (hpositive : 1 ≤ index.val) :
    (Std.Usize.wrapping_sub index 1#usize).val = index.val - 1 := by
  rw [Std.Usize.wrapping_sub_val_eq]
  have hone : (1#usize : Std.Usize).val = 1 := rfl
  rw [hone]
  have hindex := index.hSize
  have hrearrange :
      index.val + (UScalar.size .Usize - 1) =
        (index.val - 1) + UScalar.size .Usize := by omega
  rw [hrearrange, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

def GammaLoopInvariant (gamma : KernelQM31)
    (state : Array KernelQM31 19#usize × Std.Usize) : Prop :=
  2 ≤ state.2.val ∧ state.2.val ≤ 19 ∧
  ∀ index : Fin 19, index.val < state.2.val →
    KernelCanonicalQM31 (kernelArrayEntry state.1 index) ∧
    kernelQM31ToExact (kernelArrayEntry state.1 index) =
      kernelQM31ToExact gamma ^ index.val

def GammaPowerTablePost (gamma : KernelQM31)
    (powers : Array KernelQM31 19#usize) : Prop :=
  ∀ index : Fin 19,
    KernelCanonicalQM31 (kernelArrayEntry powers index) ∧
    kernelQM31ToExact (kernelArrayEntry powers index) =
      sourceGammaWeight (kernelQM31ToExact gamma) index

private theorem gamma_loop_body_transition
    (gamma : KernelQM31) (hgamma : KernelCanonicalQM31 gamma)
    (powers : Array KernelQM31 19#usize) (exponent : Std.Usize)
    (hinvariant : GammaLoopInvariant gamma (powers, exponent)) :
    ∃ flow,
      V5RelationPreparedClaimsGenerated.fri_checks.v5_gamma_powers_loop.body
          gamma powers exponent = .ok flow ∧
      match flow with
      | .done result => GammaPowerTablePost gamma result
      | .cont next =>
          GammaLoopInvariant gamma next ∧
          19 - next.2.val < 19 - exponent.val := by
  change 2 ≤ exponent.val ∧ exponent.val ≤ 19 ∧
    (∀ index : Fin 19, index.val < exponent.val →
      KernelCanonicalQM31 (kernelArrayEntry powers index) ∧
      kernelQM31ToExact (kernelArrayEntry powers index) =
        kernelQM31ToExact gamma ^ index.val) at hinvariant
  rcases hinvariant with ⟨hlower, hupper, hpowers⟩
  by_cases hactive : exponent.val < 19
  · have hcondition : exponent <
        V5RelationPreparedClaimsGenerated.fri_checks.V5_FRI_TOTAL_COLUMNS := by
      simpa [V5RelationPreparedClaimsGenerated.fri_checks.V5_FRI_TOTAL_COLUMNS]
        using hactive
    have hbit : (exponent &&& 1#usize).val = exponent.val % 2 := by
      simp
    have hnextVal := kernel_usize_wrapping_add_one_val exponent hactive
    let nextExponent := Std.Usize.wrapping_add exponent 1#usize
    have hnextVal' : nextExponent.val = exponent.val + 1 := hnextVal
    have hnextBound : nextExponent.val ≤ 19 := by omega
    have hnextDecrease : 19 - nextExponent.val < 19 - exponent.val := by
      omega
    by_cases heven : exponent.val % 2 = 0
    · have hbitZero : exponent &&& 1#usize = 0#usize := by
        apply UScalar.eq_of_val_eq
        simpa [hbit, heven]
      rcases UScalar.div_spec exponent (y := 2#usize) (by norm_num) with
        ⟨half, hhalfRun, hhalfVal⟩
      norm_num at hhalfVal
      have hhalfLt : half.val < 19 := by omega
      have hhalfBefore : half.val < exponent.val := by
        rw [hhalfVal]
        omega
      have hhalfEntry := hpowers ⟨half.val, hhalfLt⟩ hhalfBefore
      have hindexRun := kernel_array_index_call powers half hhalfLt
      rcases extracted_kernel_qm31_square_corresponds
          (kernelArrayEntry powers ⟨half.val, hhalfLt⟩)
          hhalfEntry.1 with ⟨value, hvalueRun, hvalueCanonical, hvalueExact⟩
      have hvaluePower :
          kernelQM31ToExact value =
            kernelQM31ToExact gamma ^ exponent.val := by
        have hhalfExact :
            kernelQM31ToExact
                (kernelArrayEntry powers ⟨half.val, hhalfLt⟩) =
              kernelQM31ToExact gamma ^ half.val := hhalfEntry.2
        calc
          kernelQM31ToExact value =
              kernelQM31ToExact
                  (kernelArrayEntry powers ⟨half.val, hhalfLt⟩) *
                kernelQM31ToExact
                  (kernelArrayEntry powers ⟨half.val, hhalfLt⟩) :=
            hvalueExact
          _ = (kernelQM31ToExact gamma ^ half.val) *
                (kernelQM31ToExact gamma ^ half.val) :=
            congrArg₂ (fun left right => left * right)
              hhalfExact hhalfExact
          _ = kernelQM31ToExact gamma ^ exponent.val := by
            rw [← pow_two, ← pow_mul]
            congr 1
            omega
      have hupdateRun := kernel_array_update_call powers exponent hactive value
      let nextPowers := powers.set exponent value
      have hnextInvariant :
          GammaLoopInvariant gamma (nextPowers, nextExponent) := by
        change 2 ≤ nextExponent.val ∧ nextExponent.val ≤ 19 ∧ _
        refine ⟨by omega, hnextBound, ?_⟩
        intro index hindex
        change index.val < nextExponent.val at hindex
        by_cases hsame : exponent.val = index.val
        · have hindexEq : index = ⟨exponent.val, hactive⟩ := Fin.ext hsame.symm
          subst index
          change KernelCanonicalQM31
              (kernelArrayEntry (powers.set exponent value)
                ⟨exponent.val, hactive⟩) ∧
            kernelQM31ToExact
                (kernelArrayEntry (powers.set exponent value)
                  ⟨exponent.val, hactive⟩) =
              kernelQM31ToExact gamma ^ exponent.val
          rw [kernel_array_entry_set_self]
          exact ⟨hvalueCanonical, hvaluePower⟩
        · have hbefore : index.val < exponent.val := by omega
          change KernelCanonicalQM31
              (kernelArrayEntry (powers.set exponent value) index) ∧
            kernelQM31ToExact
                (kernelArrayEntry (powers.set exponent value) index) =
              kernelQM31ToExact gamma ^ index.val
          rw [kernel_array_entry_set_other powers exponent value index hsame]
          exact hpowers index hbefore
      refine ⟨.cont (nextPowers, nextExponent), ?_, hnextInvariant,
        hnextDecrease⟩
      unfold V5RelationPreparedClaimsGenerated.fri_checks.v5_gamma_powers_loop.body
      rw [if_pos hcondition]
      simp only [Std.lift, bind_tc_ok, hbitZero, if_pos]
      rw [hhalfRun]
      simp only [bind_tc_ok]
      rw [hindexRun]
      simp only [bind_tc_ok]
      rw [hvalueRun]
      simp only [bind_tc_ok]
      rw [hupdateRun]
      simp only [bind_tc_ok]
      rfl
    · have hmodlt : exponent.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hodd : exponent.val % 2 = 1 := by omega
      have hbitOne : exponent &&& 1#usize = 1#usize := by
        apply UScalar.eq_of_val_eq
        simpa [hbit, hodd]
      let previous := Std.Usize.wrapping_sub exponent 1#usize
      have hpreviousVal : previous.val = exponent.val - 1 :=
        kernel_usize_wrapping_sub_one_val exponent (by omega)
      have hpreviousLt : previous.val < 19 := by omega
      have hpreviousBefore : previous.val < exponent.val := by omega
      have hpreviousEntry :=
        hpowers ⟨previous.val, hpreviousLt⟩ hpreviousBefore
      have hindexRun := kernel_array_index_call powers previous hpreviousLt
      rcases extracted_kernel_qm31_mul_corresponds
          (kernelArrayEntry powers ⟨previous.val, hpreviousLt⟩) gamma
          hpreviousEntry.1 hgamma with
        ⟨value, hvalueRun, hvalueCanonical, hvalueExact⟩
      have hvaluePower :
          kernelQM31ToExact value =
            kernelQM31ToExact gamma ^ exponent.val := by
        have hpreviousExact :
            kernelQM31ToExact
                (kernelArrayEntry powers
                  ⟨previous.val, hpreviousLt⟩) =
              kernelQM31ToExact gamma ^ previous.val := hpreviousEntry.2
        calc
          kernelQM31ToExact value =
              kernelQM31ToExact
                  (kernelArrayEntry powers
                    ⟨previous.val, hpreviousLt⟩) *
                kernelQM31ToExact gamma := hvalueExact
          _ = kernelQM31ToExact gamma ^ previous.val *
                kernelQM31ToExact gamma :=
            congrArg (fun left => left * kernelQM31ToExact gamma)
              hpreviousExact
          _ = kernelQM31ToExact gamma ^ exponent.val := by
            rw [← pow_succ]
            congr 1
            omega
      have hupdateRun := kernel_array_update_call powers exponent hactive value
      let nextPowers := powers.set exponent value
      have hnextInvariant :
          GammaLoopInvariant gamma (nextPowers, nextExponent) := by
        change 2 ≤ nextExponent.val ∧ nextExponent.val ≤ 19 ∧ _
        refine ⟨by omega, hnextBound, ?_⟩
        intro index hindex
        change index.val < nextExponent.val at hindex
        by_cases hsame : exponent.val = index.val
        · have hindexEq : index = ⟨exponent.val, hactive⟩ := Fin.ext hsame.symm
          subst index
          change KernelCanonicalQM31
              (kernelArrayEntry (powers.set exponent value)
                ⟨exponent.val, hactive⟩) ∧
            kernelQM31ToExact
                (kernelArrayEntry (powers.set exponent value)
                  ⟨exponent.val, hactive⟩) =
              kernelQM31ToExact gamma ^ exponent.val
          rw [kernel_array_entry_set_self]
          exact ⟨hvalueCanonical, hvaluePower⟩
        · have hbefore : index.val < exponent.val := by omega
          change KernelCanonicalQM31
              (kernelArrayEntry (powers.set exponent value) index) ∧
            kernelQM31ToExact
                (kernelArrayEntry (powers.set exponent value) index) =
              kernelQM31ToExact gamma ^ index.val
          rw [kernel_array_entry_set_other powers exponent value index hsame]
          exact hpowers index hbefore
      refine ⟨.cont (nextPowers, nextExponent), ?_, hnextInvariant,
        hnextDecrease⟩
      unfold V5RelationPreparedClaimsGenerated.fri_checks.v5_gamma_powers_loop.body
      rw [if_pos hcondition]
      simp only [Std.lift, bind_tc_ok, hbitOne, if_neg]
      rw [hindexRun]
      simp only [bind_tc_ok]
      rw [hvalueRun]
      simp only [bind_tc_ok]
      rw [hupdateRun]
      simp only [bind_tc_ok]
      rfl
  · have hexponent : exponent.val = 19 := by omega
    have hcondition : ¬ exponent <
        V5RelationPreparedClaimsGenerated.fri_checks.V5_FRI_TOTAL_COLUMNS := by
      simpa [V5RelationPreparedClaimsGenerated.fri_checks.V5_FRI_TOTAL_COLUMNS]
        using hactive
    refine ⟨.done powers, ?_, ?_⟩
    · simp [V5RelationPreparedClaimsGenerated.fri_checks.v5_gamma_powers_loop.body,
        hcondition]
    · intro index
      have hentry := hpowers index (by omega)
      simpa [sourceGammaWeight] using hentry

private theorem extracted_gamma_loop_corresponds
    (gamma : KernelQM31) (hgamma : KernelCanonicalQM31 gamma)
    (powers : Array KernelQM31 19#usize) (exponent : Std.Usize)
    (hinvariant : GammaLoopInvariant gamma (powers, exponent)) :
    ∃ result : Array KernelQM31 19#usize,
      V5RelationPreparedClaimsGenerated.fri_checks.v5_gamma_powers_loop
          gamma powers exponent = .ok result ∧
      GammaPowerTablePost gamma result := by
  have hspec : Aeneas.Std.WP.spec
      (V5RelationPreparedClaimsGenerated.fri_checks.v5_gamma_powers_loop
        gamma powers exponent)
      (GammaPowerTablePost gamma) := by
    unfold V5RelationPreparedClaimsGenerated.fri_checks.v5_gamma_powers_loop
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun state : Array KernelQM31 19#usize × Std.Usize =>
        19 - state.2.val)
      (inv := GammaLoopInvariant gamma)
    · rintro ⟨nextPowers, nextExponent⟩ hstate
      simp only
      apply Aeneas.Std.WP.exists_imp_spec
      rcases gamma_loop_body_transition gamma hgamma nextPowers nextExponent
          hstate with ⟨flow, hflow, hpost⟩
      refine ⟨flow, hflow, ?_⟩
      cases flow <;> exact hpost
    · exact hinvariant
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨result, hrun, hpost⟩
  exact ⟨result, hrun, hpost⟩

private theorem kernel_zero_canonical :
    KernelCanonicalQM31
      V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ZERO := by
  rw [V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ZERO]
  norm_num [KernelCanonicalQM31, KernelCanonicalCM31,
    KernelCanonicalM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem kernel_zero_exact :
    kernelQM31ToExact
      V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ZERO = 0 := by
  rw [V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ZERO]
  rfl

private theorem kernel_one_canonical :
    KernelCanonicalQM31
      V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ONE := by
  rw [V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ONE]
  norm_num [KernelCanonicalQM31, KernelCanonicalCM31,
    KernelCanonicalM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem kernel_one_exact :
    kernelQM31ToExact
      V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ONE = 1 := by
  rw [V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ONE]
  rfl

/-- For every canonical production gamma, the complete generated Rust helper
terminates successfully and every one of its nineteen entries is exactly the
maintained `gamma^lane` weight. -/
theorem extracted_gamma_powers_eq_source_weights
    (gamma : KernelQM31) (hgamma : KernelCanonicalQM31 gamma) :
    ∃ powers : Array KernelQM31 19#usize,
      V5RelationPreparedClaimsGenerated.fri_checks.v5_gamma_powers gamma =
        .ok powers ∧
      GammaPowerTablePost gamma powers := by
  let initial : Array KernelQM31 19#usize :=
    Array.repeat 19#usize
      V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ZERO
  let afterZero := initial.set 0#usize
    V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ONE
  let afterOne := afterZero.set 1#usize gamma
  have hupdateZero :
      Array.update initial 0#usize
          V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ONE =
        .ok afterZero := by
    simpa [afterZero] using kernel_array_update_call initial 0#usize
      (by norm_num)
      V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ONE
  have hupdateOne : Array.update afterZero 1#usize gamma = .ok afterOne := by
    simpa [afterOne] using kernel_array_update_call afterZero 1#usize
      (by norm_num) gamma
  have hinitial : GammaLoopInvariant gamma (afterOne, 2#usize) := by
    change 2 ≤ (2#usize : Std.Usize).val ∧
      (2#usize : Std.Usize).val ≤ 19 ∧
      (∀ index : Fin 19, index.val < (2#usize : Std.Usize).val →
        KernelCanonicalQM31 (kernelArrayEntry afterOne index) ∧
        kernelQM31ToExact (kernelArrayEntry afterOne index) =
          kernelQM31ToExact gamma ^ index.val)
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro index hindex
    norm_num at hindex
    have hcases : index.val = 0 ∨ index.val = 1 := by omega
    rcases hcases with hzero | hone
    · have hneOne : (1#usize : Std.Usize).val ≠ index.val := by
        norm_num [hzero]
      have hindexZero : index = ⟨0, by decide⟩ := Fin.ext hzero
      subst index
      unfold kernelArrayEntry
      dsimp only [afterOne, afterZero]
      simp [Array.set_val_eq, kernel_one_canonical, kernel_one_exact]
    · have hindexOne : index = ⟨1, by decide⟩ := Fin.ext hone
      subst index
      unfold kernelArrayEntry
      dsimp only [afterOne]
      simp [Array.set_val_eq, hgamma]
  rcases extracted_gamma_loop_corresponds gamma hgamma afterOne 2#usize
      hinitial with ⟨powers, hloop, hpost⟩
  refine ⟨powers, ?_, hpost⟩
  unfold V5RelationPreparedClaimsGenerated.fri_checks.v5_gamma_powers
  change (do
    let powers ← Array.update initial 0#usize
      V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ONE
    let powers ← Array.update powers 1#usize gamma
    V5RelationPreparedClaimsGenerated.fri_checks.v5_gamma_powers_loop
      gamma powers 2#usize) = .ok powers
  rw [hupdateZero]
  simp only [bind_tc_ok]
  rw [hupdateOne]
  simp only [bind_tc_ok]
  exact hloop

/-! ## Exact extracted bounded dot-product kernel -/

abbrev kernelM31Modulus : Nat := 2147483647
abbrev kernelU64Cardinality : Nat := 2 ^ 64
abbrev kernelChannelProductBound : Nat :=
  (kernelM31Modulus - 1) ^ 2

theorem four_kernel_channel_products_fit_u64 :
    4 * kernelChannelProductBound < kernelU64Cardinality := by
  norm_num [kernelChannelProductBound, kernelM31Modulus,
    kernelU64Cardinality]

def kernelRowCell (row : Array Std.U64 3#usize) (channel : Nat) : Std.U64 :=
  row.val[channel]!

def kernelMatrixCell
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (component channel : Nat) : Std.U64 :=
  kernelRowCell sums.val[component]! channel

def kernelChannelM31
    (components : Array (Array KernelM31 3#usize) 3#usize)
    (component channel : Nat) : KernelM31 :=
  components.val[component]!.val[channel]!

def KernelCanonicalChannelMatrix
    (components : Array (Array KernelM31 3#usize) 3#usize) : Prop :=
  ∀ component, component < 3 → ∀ channel, channel < 3 →
    KernelCanonicalM31 (kernelChannelM31 components component channel).val

def kernelGeneratedComponentMatrix
    (q : KernelQM31) (qsum : KernelCM31) (m0 m1 m2 : KernelM31) :
    Array (Array KernelM31 3#usize) 3#usize :=
  Array.make 3#usize [
    Array.make 3#usize [q.c0.a, q.c0.b, m0],
    Array.make 3#usize [q.c1.a, q.c1.b, m1],
    Array.make 3#usize [qsum.a, qsum.b, m2]
  ]

def kernelExactCMChannel (x : KernelCM31Exact) (channel : Nat) :
    KernelM31Exact :=
  if channel = 0 then x.re else if channel = 1 then x.im else x.re + x.im

def kernelExactQMComponent (x : KernelQM31Exact) (component : Nat) :
    KernelCM31Exact :=
  if component = 0 then x.re else if component = 1 then x.im else x.re + x.im

def kernelExactInputChannel (q : KernelQM31) (component channel : Nat) :
    KernelM31Exact :=
  kernelExactCMChannel
    (kernelExactQMComponent (kernelQM31ToExact q) component) channel

private theorem kernel_generated_component_matrix_canonical
    (q : KernelQM31) (qsum : KernelCM31) (m0 m1 m2 : KernelM31)
    (hq : KernelCanonicalQM31 q)
    (hqsum : KernelCanonicalCM31 qsum)
    (hm0 : KernelCanonicalM31 m0.val)
    (hm1 : KernelCanonicalM31 m1.val)
    (hm2 : KernelCanonicalM31 m2.val) :
    KernelCanonicalChannelMatrix
      (kernelGeneratedComponentMatrix q qsum m0 m1 m2) := by
  rcases hq with ⟨⟨hc0a, hc0b⟩, ⟨hc1a, hc1b⟩⟩
  rcases hqsum with ⟨hsuma, hsumb⟩
  intro component hComponent channel hChannel
  have hc : component = 0 ∨ component = 1 ∨ component = 2 := by omega
  have hh : channel = 0 ∨ channel = 1 ∨ channel = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl
  all_goals
    simp only [kernelChannelM31, kernelGeneratedComponentMatrix,
      Aeneas.Std.Array.make]
  all_goals assumption

private theorem kernel_generated_component_matrix_exact
    (q : KernelQM31) (qsum : KernelCM31) (m0 m1 m2 : KernelM31)
    (hqsumExact :
      kernelCM31ToExact qsum =
        kernelCM31ToExact q.c0 + kernelCM31ToExact q.c1)
    (hm0Exact : ((m0.val : Nat) : KernelM31Exact) =
      ((q.c0.a.val : Nat) : KernelM31Exact) +
        ((q.c0.b.val : Nat) : KernelM31Exact))
    (hm1Exact : ((m1.val : Nat) : KernelM31Exact) =
      ((q.c1.a.val : Nat) : KernelM31Exact) +
        ((q.c1.b.val : Nat) : KernelM31Exact))
    (hm2Exact : ((m2.val : Nat) : KernelM31Exact) =
      ((qsum.a.val : Nat) : KernelM31Exact) +
        ((qsum.b.val : Nat) : KernelM31Exact)) :
    ∀ component, component < 3 → ∀ channel, channel < 3 →
      (((kernelChannelM31
        (kernelGeneratedComponentMatrix q qsum m0 m1 m2)
        component channel).val : Nat) : KernelM31Exact) =
        kernelExactInputChannel q component channel := by
  intro component hComponent channel hChannel
  have hqsumRe := congrArg (fun x : KernelCM31Exact => x.re) hqsumExact
  have hqsumIm := congrArg (fun x : KernelCM31Exact => x.im) hqsumExact
  change (((qsum.a.val : Nat) : KernelM31Exact) =
    ((q.c0.a.val : Nat) : KernelM31Exact) +
      ((q.c1.a.val : Nat) : KernelM31Exact)) at hqsumRe
  change (((qsum.b.val : Nat) : KernelM31Exact) =
    ((q.c0.b.val : Nat) : KernelM31Exact) +
      ((q.c1.b.val : Nat) : KernelM31Exact)) at hqsumIm
  have hc : component = 0 ∨ component = 1 ∨ component = 2 := by omega
  have hh : channel = 0 ∨ channel = 1 ∨ channel = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl
  all_goals
    simp only [kernelChannelM31, kernelGeneratedComponentMatrix,
      Aeneas.Std.Array.make]
  all_goals
    simp [kernelExactInputChannel, kernelExactQMComponent,
      kernelExactCMChannel, kernelQM31ToExact, kernelCM31ToExact] at hqsumExact ⊢
  all_goals try exact hm0Exact
  all_goals try exact hm1Exact
  all_goals try rw [hm2Exact]
  all_goals try rw [hqsumRe]
  all_goals try rw [hqsumIm]

private theorem kernel_list_get_eq_getElemBang
    {T : Type} [Inhabited T]
    (values : List T) (index : Nat) (hindex : index < values.length) :
    values[index] = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem kernel_generic_array_index_call
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = .ok values.val[index.val]! := by
  obtain ⟨value, hrun, hvalue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have harrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have helem := kernel_list_get_eq_getElemBang values.val index.val harrayBound
  simpa [hvalue, helem] using hrun

private theorem kernel_generic_array_index_mut_call
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_mut_usize values index =
      .ok (values.val[index.val]!, values.set index) := by
  obtain ⟨result, hrun, hpost⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_mut_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  rcases result with ⟨value, back⟩
  rcases hpost with ⟨hvalue, hback⟩
  have harrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have helem := kernel_list_get_eq_getElemBang values.val index.val harrayBound
  simpa [hvalue, hback, helem] using hrun

private theorem kernel_generic_array_update_call
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T)
    (hindex : index.val < N.val) :
    Array.update values index value = .ok (values.set index value) := by
  obtain ⟨out, hrun, hout⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec values index value (by
      simpa [Array.length_eq] using hindex))
  simpa [hout] using hrun

def kernelAccumulatedChannelValue
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (component channel : Std.Usize) : Std.U64 :=
  Std.U64.wrapping_add
    (kernelMatrixCell sums component.val channel.val)
    (Std.U64.wrapping_mul
      (UScalar.cast .U64
        (kernelChannelM31 leftComponents component.val channel.val))
      (UScalar.cast .U64
        (kernelChannelM31 rightComponents component.val channel.val)))

def kernelAccumulateChannel
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (component channel : Std.Usize) :
    Array (Array Std.U64 3#usize) 3#usize :=
  sums.set component
    ((sums.val[component.val]!).set channel
      (kernelAccumulatedChannelValue sums leftComponents rightComponents
        component channel))

def KernelChannelUpdateInvariant
    (base current : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (component processed : Nat) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (kernelMatrixCell current row channel).val =
      if row = component ∧ channel < processed then
        (kernelMatrixCell base row channel).val +
          (kernelChannelM31 leftComponents row channel).val *
          (kernelChannelM31 rightComponents row channel).val
      else
        (kernelMatrixCell base row channel).val

private theorem kernel_u32_channel_product_no_wrap
    (left right : KernelM31) :
    (Std.U64.wrapping_mul (UScalar.cast .U64 left)
      (UScalar.cast .U64 right)).val = left.val * right.val := by
  rw [Std.U64.wrapping_mul_val_eq,
    U32.cast_U64_val_eq, U32.cast_U64_val_eq]
  have hl := UScalar.hBounds left
  have hr := UScalar.hBounds right
  have hproduct : left.val * right.val < UScalar.size .U64 := by
    rw [UScalar.size, UScalarTy.U64_numBits_eq]
    norm_num at hl hr ⊢
    nlinarith
  exact Nat.mod_eq_of_lt hproduct

private theorem kernel_accumulated_channel_value_no_wrap
    (base : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (hbound :
      (kernelMatrixCell base component.val channel.val).val +
        (kernelChannelM31 leftComponents component.val channel.val).val *
        (kernelChannelM31 rightComponents component.val channel.val).val <
          kernelU64Cardinality) :
    (kernelAccumulatedChannelValue base leftComponents rightComponents
      component channel).val =
      (kernelMatrixCell base component.val channel.val).val +
        (kernelChannelM31 leftComponents component.val channel.val).val *
        (kernelChannelM31 rightComponents component.val channel.val).val := by
  unfold kernelAccumulatedChannelValue
  rw [Std.U64.wrapping_add_val_eq, kernel_u32_channel_product_no_wrap]
  have hsize : UScalar.size .U64 = kernelU64Cardinality := by
    exact AspisAeneasM31ReduceU64.u64_size_eq
  rw [hsize]
  exact Nat.mod_eq_of_lt hbound

private theorem kernel_matrix_cell_accumulate_same
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (hcomponent : component.val < 3) (hchannel : channel.val < 3) :
    kernelMatrixCell
        (kernelAccumulateChannel sums leftComponents rightComponents
          component channel)
        component.val channel.val =
      kernelAccumulatedChannelValue sums leftComponents rightComponents
        component channel := by
  unfold kernelMatrixCell kernelRowCell kernelAccumulateChannel
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using hcomponent, rfl⟩)]
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using hchannel, rfl⟩)]

private theorem kernel_matrix_cell_accumulate_frame
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (row column : Nat) (hrow : row < 3) (_hcolumn : column < 3)
    (hdifferent : row ≠ component.val ∨ column ≠ channel.val) :
    kernelMatrixCell
        (kernelAccumulateChannel sums leftComponents rightComponents
          component channel)
        row column = kernelMatrixCell sums row column := by
  unfold kernelMatrixCell kernelRowCell kernelAccumulateChannel
  simp only [Array.set_val_eq]
  by_cases hsameRow : row = component.val
  · subst row
    rw [List.set_getElem!_eq _ _ _ _ (by
      exact ⟨by simpa [Array.length_eq] using hrow, rfl⟩)]
    simp only [Array.set_val_eq]
    rw [List.set_getElem!_ne _ _ _ _ (by omega)]
  · rw [List.set_getElem!_ne _ _ _ _ (by omega)]

private theorem kernel_channel_update_invariant_step
    (base current : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (hcomponent : component.val < 3) (hchannel : channel.val < 3)
    (hinvariant : KernelChannelUpdateInvariant base current leftComponents
      rightComponents component.val channel.val)
    (hnoOverflow :
      (kernelMatrixCell base component.val channel.val).val +
        (kernelChannelM31 leftComponents component.val channel.val).val *
        (kernelChannelM31 rightComponents component.val channel.val).val <
          kernelU64Cardinality) :
    KernelChannelUpdateInvariant base
      (kernelAccumulateChannel current leftComponents rightComponents
        component channel)
      leftComponents rightComponents component.val (channel.val + 1) := by
  intro row hrow column hcolumn
  by_cases hsameRow : row = component.val
  · by_cases hsameColumn : column = channel.val
    · subst row
      subst column
      rw [kernel_matrix_cell_accumulate_same current leftComponents
        rightComponents component channel hcomponent hchannel]
      have hold := hinvariant component.val hcomponent channel.val hchannel
      simp at hold
      rw [kernel_accumulated_channel_value_no_wrap current leftComponents
        rightComponents component channel]
      · rw [hold]
        simp
      · rw [hold]
        exact hnoOverflow
    · rw [kernel_matrix_cell_accumulate_frame current leftComponents
        rightComponents component channel row column hrow hcolumn
        (Or.inr hsameColumn)]
      have hold := hinvariant row hrow column hcolumn
      rw [hold]
      simp only [hsameRow, true_and]
      by_cases hbefore : column < channel.val
      · have hafter : column < channel.val + 1 := by omega
        rw [if_pos hbefore, if_pos hafter]
      · have hafter : ¬ column < channel.val + 1 := by omega
        rw [if_neg hbefore, if_neg hafter]
  · rw [kernel_matrix_cell_accumulate_frame current leftComponents
      rightComponents component channel row column hrow hcolumn
      (Or.inl hsameRow)]
    have hold := hinvariant row hrow column hcolumn
    rw [hold]
    simp [hsameRow]

private theorem kernel_dot_channel_body_active
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (component : Std.Usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (channel : Std.Usize)
    (hcomponent : component.val < 3) (hchannel : channel.val < 3) :
    ∃ next,
      V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0_loop0_loop0.body
          leftComponents rightComponents component sums channel =
        .ok (.cont
          (kernelAccumulateChannel sums leftComponents rightComponents
            component channel, next)) ∧
      next.val = channel.val + 1 := by
  have hleftRow := kernel_generic_array_index_call
    leftComponents component hcomponent
  have hleft := kernel_generic_array_index_call
    leftComponents.val[component.val]! channel hchannel
  have hrightRow := kernel_generic_array_index_call
    rightComponents component hcomponent
  have hright := kernel_generic_array_index_call
    rightComponents.val[component.val]! channel hchannel
  have hsumsRow := kernel_generic_array_index_call sums component hcomponent
  have hsumsValue := kernel_generic_array_index_call
    sums.val[component.val]! channel hchannel
  have hsumsMut := kernel_generic_array_index_mut_call sums component hcomponent
  have hrowUpdate := kernel_generic_array_update_call
    sums.val[component.val]! channel
      (kernelAccumulatedChannelValue sums leftComponents rightComponents
        component channel) hchannel
  let next := Std.Usize.wrapping_add channel 1#usize
  have hnext : next.val = channel.val + 1 :=
    kernel_usize_wrapping_add_one_val channel (by omega)
  refine ⟨next, ?_, hnext⟩
  unfold
    V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0_loop0_loop0.body
  simp only [show channel < 3#usize from hchannel, if_pos,
    hleftRow, hleft, hrightRow, hright, hsumsRow, hsumsValue, hsumsMut,
    bind_tc_ok, Std.lift]
  change
    (do
      let a4 ← Array.update sums.val[component.val]! channel
        (kernelAccumulatedChannelValue sums leftComponents rightComponents
          component channel)
      ok (cont ((sums.set component) a4,
        Std.Usize.wrapping_add channel 1#usize))) =
      ok (cont (kernelAccumulateChannel sums leftComponents rightComponents
        component channel, next))
  rw [hrowUpdate]
  simp only [bind_tc_ok]
  rfl

private theorem kernel_dot_channel_body_done
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (component : Std.Usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (channel : Std.Usize) (hdone : ¬ channel.val < 3) :
    V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0_loop0_loop0.body
        leftComponents rightComponents component sums channel =
      .ok (.done sums) := by
  unfold
    V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0_loop0_loop0.body
  simp [hdone]

theorem extracted_dot_channel_loop_corresponds
    (base : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (component : Std.Usize) (hcomponent : component.val < 3)
    (hnoOverflow : ∀ channel, channel < 3 →
      (kernelMatrixCell base component.val channel).val +
        (kernelChannelM31 leftComponents component.val channel).val *
        (kernelChannelM31 rightComponents component.val channel).val <
          kernelU64Cardinality) :
    V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0_loop0_loop0
        base leftComponents rightComponents component 0#usize
      ⦃ out => KernelChannelUpdateInvariant base out leftComponents
        rightComponents component.val 3 ⦄ := by
  simp only [V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : Array (Array Std.U64 3#usize) 3#usize × Std.Usize =>
      3 - state.2.val)
    (fun state => state.2.val ≤ 3 ∧
      KernelChannelUpdateInvariant base state.1 leftComponents
        rightComponents component.val state.2.val)
    (fun out => KernelChannelUpdateInvariant base out leftComponents
      rightComponents component.val 3)
  · rintro ⟨current, channel⟩ ⟨hchannelLe, hinvariant⟩
    dsimp only at hchannelLe hinvariant ⊢
    by_cases hactive : channel.val < 3
    · obtain ⟨next, hbody, hnext⟩ :=
        kernel_dot_channel_body_active leftComponents rightComponents
          component current channel hcomponent hactive
      rw [hbody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hnext]
        omega
      · rw [hnext]
        exact kernel_channel_update_invariant_step base current
          leftComponents rightComponents component channel hcomponent hactive
          hinvariant (hnoOverflow channel.val hactive)
      · rw [hnext]
        omega
    · have hatEnd : channel.val = 3 := by omega
      rw [kernel_dot_channel_body_done leftComponents rightComponents
        component current channel hactive]
      simpa [hatEnd] using hinvariant
  · refine ⟨by norm_num, ?_⟩
    intro row hrow channel hchannel
    simp

def KernelComponentUpdateInvariant
    (base current : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (processed : Nat) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (kernelMatrixCell current row channel).val =
      if row < processed then
        (kernelMatrixCell base row channel).val +
          (kernelChannelM31 leftComponents row channel).val *
          (kernelChannelM31 rightComponents row channel).val
      else
        (kernelMatrixCell base row channel).val

private theorem kernel_component_update_invariant_step
    (base current out : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (component : Std.Usize) (_hcomponent : component.val < 3)
    (houter : KernelComponentUpdateInvariant base current leftComponents
      rightComponents component.val)
    (hinner : KernelChannelUpdateInvariant current out leftComponents
      rightComponents component.val 3) :
    KernelComponentUpdateInvariant base out leftComponents rightComponents
      (component.val + 1) := by
  intro row hrow channel hchannel
  have hinnerCell := hinner row hrow channel hchannel
  have houterCell := houter row hrow channel hchannel
  by_cases hsame : row = component.val
  · subst row
    simp at houterCell
    simp [houterCell, hchannel] at hinnerCell
    simpa using hinnerCell
  · have hframe :
        (kernelMatrixCell out row channel).val =
          (kernelMatrixCell current row channel).val := by
      simpa [hsame] using hinnerCell
    rw [hframe, houterCell]
    by_cases hbefore : row < component.val
    · have hafter : row < component.val + 1 := by omega
      rw [if_pos hbefore, if_pos hafter]
    · have hafter : ¬ row < component.val + 1 := by omega
      rw [if_neg hbefore, if_neg hafter]

private theorem kernel_dot_component_body_active
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (component : Std.Usize) (hcomponent : component.val < 3)
    (hnoOverflow : ∀ channel, channel < 3 →
      (kernelMatrixCell sums component.val channel).val +
        (kernelChannelM31 leftComponents component.val channel).val *
        (kernelChannelM31 rightComponents component.val channel).val <
          kernelU64Cardinality) :
    ∃ next out,
      V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0_loop0.body
          leftComponents rightComponents sums component =
        .ok (.cont (out, next)) ∧
      next.val = component.val + 1 ∧
      KernelChannelUpdateInvariant sums out leftComponents rightComponents
        component.val 3 := by
  have hchannelSpec := extracted_dot_channel_loop_corresponds sums
    leftComponents rightComponents component hcomponent hnoOverflow
  obtain ⟨out, hchannelRun, hchannelPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists hchannelSpec
  let next := Std.Usize.wrapping_add component 1#usize
  have hnext : next.val = component.val + 1 :=
    kernel_usize_wrapping_add_one_val component (by omega)
  refine ⟨next, out, ?_, hnext, hchannelPost⟩
  unfold
    V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0_loop0.body
  simp only [show component < 3#usize from hcomponent, if_pos]
  rw [hchannelRun]
  simp only [bind_tc_ok, Std.lift]
  rfl

private theorem kernel_dot_component_body_done
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (component : Std.Usize) (hdone : ¬ component.val < 3) :
    V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0_loop0.body
        leftComponents rightComponents sums component =
      .ok (.done sums) := by
  unfold
    V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0_loop0.body
  simp [hdone]

theorem extracted_dot_component_loop_corresponds
    (base : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents :
      Array (Array KernelM31 3#usize) 3#usize)
    (hnoOverflow : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (kernelMatrixCell base row channel).val +
        (kernelChannelM31 leftComponents row channel).val *
        (kernelChannelM31 rightComponents row channel).val <
          kernelU64Cardinality) :
    V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0_loop0
        base leftComponents rightComponents 0#usize
      ⦃ out => KernelComponentUpdateInvariant base out leftComponents
        rightComponents 3 ⦄ := by
  simp only [V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : Array (Array Std.U64 3#usize) 3#usize × Std.Usize =>
      3 - state.2.val)
    (fun state => state.2.val ≤ 3 ∧
      KernelComponentUpdateInvariant base state.1 leftComponents
        rightComponents state.2.val)
    (fun out => KernelComponentUpdateInvariant base out leftComponents
      rightComponents 3)
  · rintro ⟨current, component⟩ ⟨hcomponentLe, hinvariant⟩
    dsimp only at hcomponentLe hinvariant ⊢
    by_cases hactive : component.val < 3
    · have hcurrentNoOverflow : ∀ channel, channel < 3 →
          (kernelMatrixCell current component.val channel).val +
            (kernelChannelM31 leftComponents component.val channel).val *
            (kernelChannelM31 rightComponents component.val channel).val <
              kernelU64Cardinality := by
        intro channel hchannel
        have hcurrent := hinvariant component.val hactive channel hchannel
        have hnotBefore : ¬ component.val < component.val := by omega
        rw [if_neg hnotBefore] at hcurrent
        rw [hcurrent]
        exact hnoOverflow component.val hactive channel hchannel
      obtain ⟨next, out, hbody, hnext, hinner⟩ :=
        kernel_dot_component_body_active leftComponents rightComponents
          current component hactive hcurrentNoOverflow
      rw [hbody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hnext]
        omega
      · rw [hnext]
        exact kernel_component_update_invariant_step base current out
          leftComponents rightComponents component hactive hinvariant hinner
      · rw [hnext]
        omega
    · have hatEnd : component.val = 3 := by omega
      rw [kernel_dot_component_body_done leftComponents rightComponents
        current component hactive]
      simpa [hatEnd] using hinvariant
  · refine ⟨by norm_num, ?_⟩
    intro row hrow channel hchannel
    simp

def KernelSingleProductPost
    (before after : Array (Array Std.U64 3#usize) 3#usize)
    (left right : KernelQM31) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (kernelMatrixCell after row channel).val ≤
        (kernelMatrixCell before row channel).val +
          kernelChannelProductBound ∧
    (((kernelMatrixCell after row channel).val : Nat) : KernelM31Exact) =
      (((kernelMatrixCell before row channel).val : Nat) : KernelM31Exact) +
        kernelExactInputChannel left row channel *
          kernelExactInputChannel right row channel

private theorem extracted_dot_pair_channels_corresponds
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (left right : KernelQM31)
    (hleft : KernelCanonicalQM31 left)
    (hright : KernelCanonicalQM31 right)
    (hspace : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (kernelMatrixCell current row channel).val +
        kernelChannelProductBound < kernelU64Cardinality) :
    ∃ out,
      (do
        let leftSum ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.add
            left.c0 left.c1
        let rightSum ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.add
            right.c0 right.c1
        let lm0 ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.add
            left.c0.a left.c0.b
        let lm1 ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.add
            left.c1.a left.c1.b
        let lm2 ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.add
            leftSum.a leftSum.b
        let rm0 ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.add
            right.c0.a right.c0.b
        let rm1 ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.add
            right.c1.a right.c1.b
        let rm2 ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.add
            rightSum.a rightSum.b
        V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0_loop0
          current
          (kernelGeneratedComponentMatrix left leftSum lm0 lm1 lm2)
          (kernelGeneratedComponentMatrix right rightSum rm0 rm1 rm2)
          0#usize) = .ok out ∧
      KernelSingleProductPost current out left right := by
  rcases kernel_cm31_add_corresponds left.c0 left.c1 hleft.1 hleft.2 with
    ⟨leftSum, hleftSum, hleftSumCanonical, hleftSumExact⟩
  rcases kernel_cm31_add_corresponds right.c0 right.c1
      hright.1 hright.2 with
    ⟨rightSum, hrightSum, hrightSumCanonical, hrightSumExact⟩
  rcases kernel_m31_add_corresponds left.c0.a left.c0.b
      hleft.1.1 hleft.1.2 with
    ⟨lm0, hlm0, hlm0Canonical, hlm0Exact⟩
  rcases kernel_m31_add_corresponds left.c1.a left.c1.b
      hleft.2.1 hleft.2.2 with
    ⟨lm1, hlm1, hlm1Canonical, hlm1Exact⟩
  rcases kernel_m31_add_corresponds leftSum.a leftSum.b
      hleftSumCanonical.1 hleftSumCanonical.2 with
    ⟨lm2, hlm2, hlm2Canonical, hlm2Exact⟩
  rcases kernel_m31_add_corresponds right.c0.a right.c0.b
      hright.1.1 hright.1.2 with
    ⟨rm0, hrm0, hrm0Canonical, hrm0Exact⟩
  rcases kernel_m31_add_corresponds right.c1.a right.c1.b
      hright.2.1 hright.2.2 with
    ⟨rm1, hrm1, hrm1Canonical, hrm1Exact⟩
  rcases kernel_m31_add_corresponds rightSum.a rightSum.b
      hrightSumCanonical.1 hrightSumCanonical.2 with
    ⟨rm2, hrm2, hrm2Canonical, hrm2Exact⟩
  let leftComponents :=
    kernelGeneratedComponentMatrix left leftSum lm0 lm1 lm2
  let rightComponents :=
    kernelGeneratedComponentMatrix right rightSum rm0 rm1 rm2
  have hleftComponentsCanonical :
      KernelCanonicalChannelMatrix leftComponents :=
    kernel_generated_component_matrix_canonical left leftSum lm0 lm1 lm2
      hleft hleftSumCanonical hlm0Canonical hlm1Canonical hlm2Canonical
  have hrightComponentsCanonical :
      KernelCanonicalChannelMatrix rightComponents :=
    kernel_generated_component_matrix_canonical right rightSum rm0 rm1 rm2
      hright hrightSumCanonical hrm0Canonical hrm1Canonical hrm2Canonical
  have hleftComponentsExact := kernel_generated_component_matrix_exact
    left leftSum lm0 lm1 lm2 hleftSumExact hlm0Exact hlm1Exact hlm2Exact
  have hrightComponentsExact := kernel_generated_component_matrix_exact
    right rightSum rm0 rm1 rm2 hrightSumExact hrm0Exact hrm1Exact hrm2Exact
  have hnoOverflow : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (kernelMatrixCell current row channel).val +
        (kernelChannelM31 leftComponents row channel).val *
        (kernelChannelM31 rightComponents row channel).val <
          kernelU64Cardinality := by
    intro row hrow channel hchannel
    have hl := hleftComponentsCanonical row hrow channel hchannel
    have hr := hrightComponentsCanonical row hrow channel hchannel
    change (kernelChannelM31 leftComponents row channel).val <
      kernelM31Modulus at hl
    change (kernelChannelM31 rightComponents row channel).val <
      kernelM31Modulus at hr
    have hlle : (kernelChannelM31 leftComponents row channel).val ≤
        kernelM31Modulus - 1 := by omega
    have hrle : (kernelChannelM31 rightComponents row channel).val ≤
        kernelM31Modulus - 1 := by omega
    have hproduct :
        (kernelChannelM31 leftComponents row channel).val *
          (kernelChannelM31 rightComponents row channel).val ≤
            kernelChannelProductBound := by
      unfold kernelChannelProductBound
      simpa [pow_two] using Nat.mul_le_mul hlle hrle
    exact lt_of_le_of_lt (Nat.add_le_add_left hproduct _)
      (hspace row hrow channel hchannel)
  have hcomponentSpec := extracted_dot_component_loop_corresponds current
    leftComponents rightComponents hnoOverflow
  obtain ⟨out, hcomponentRun, hcomponentPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists hcomponentSpec
  have hpost : KernelSingleProductPost current out left right := by
    intro row hrow channel hchannel
    have hinner := hcomponentPost row hrow channel hchannel
    simp only [show row < 3 from hrow, if_pos] at hinner
    have hleftExact :
        (((kernelChannelM31 leftComponents row channel).val : Nat) :
            KernelM31Exact) =
          kernelExactInputChannel left row channel := by
      simpa [leftComponents] using
        hleftComponentsExact row hrow channel hchannel
    have hrightExact :
        (((kernelChannelM31 rightComponents row channel).val : Nat) :
            KernelM31Exact) =
          kernelExactInputChannel right row channel := by
      simpa [rightComponents] using
        hrightComponentsExact row hrow channel hchannel
    have hl := hleftComponentsCanonical row hrow channel hchannel
    have hr := hrightComponentsCanonical row hrow channel hchannel
    change (kernelChannelM31 leftComponents row channel).val <
      kernelM31Modulus at hl
    change (kernelChannelM31 rightComponents row channel).val <
      kernelM31Modulus at hr
    have hlle : (kernelChannelM31 leftComponents row channel).val ≤
        kernelM31Modulus - 1 := by omega
    have hrle : (kernelChannelM31 rightComponents row channel).val ≤
        kernelM31Modulus - 1 := by omega
    have hproduct :
        (kernelChannelM31 leftComponents row channel).val *
          (kernelChannelM31 rightComponents row channel).val ≤
            kernelChannelProductBound := by
      unfold kernelChannelProductBound
      simpa [pow_two] using Nat.mul_le_mul hlle hrle
    constructor
    · rw [hinner]
      exact Nat.add_le_add_left hproduct _
    · rw [hinner, Nat.cast_add, Nat.cast_mul, hleftExact, hrightExact]
  refine ⟨out, ?_, hpost⟩
  rw [hleftSum]
  simp only [bind_tc_ok]
  rw [hrightSum]
  simp only [bind_tc_ok]
  rw [hlm0]
  simp only [bind_tc_ok]
  rw [hlm1]
  simp only [bind_tc_ok]
  rw [hlm2]
  simp only [bind_tc_ok]
  rw [hrm0]
  simp only [bind_tc_ok]
  rw [hrm1]
  simp only [bind_tc_ok]
  rw [hrm2]
  simp only [bind_tc_ok]
  simpa [leftComponents, rightComponents] using hcomponentRun

def KernelCanonicalQM31Array19
    (values : Array KernelQM31 19#usize) : Prop :=
  ∀ index : Fin 19, KernelCanonicalQM31 (kernelArrayEntry values index)

def kernelExactChannelDotBlock
    (powers values : Array KernelQM31 19#usize)
    (start processed row channel : Nat) : KernelM31Exact :=
  ∑ offset ∈ Finset.range processed,
    kernelExactInputChannel powers.val[start + offset]! row channel *
      kernelExactInputChannel values.val[start + offset]! row channel

def KernelDotOuterInvariant
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (powers values : Array KernelQM31 19#usize)
    (start processed : Nat) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (kernelMatrixCell current row channel).val ≤
        processed * kernelChannelProductBound ∧
    (((kernelMatrixCell current row channel).val : Nat) : KernelM31Exact) =
      kernelExactChannelDotBlock powers values start processed row channel

private theorem kernel_usize_wrapping_add_val_below_nineteen
    (left right : Std.Usize) (hbound : left.val + right.val < 19) :
    (Std.Usize.wrapping_add left right).val = left.val + right.val := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have room : 19 < UScalar.size .Usize := by
    have h := (19#usize).hSize
    scalar_tac
  omega

private theorem kernel_dot_outer_body_active
    (powers values : Array KernelQM31 19#usize)
    (start count : Std.Usize)
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (index : Std.Usize)
    (hactive : index.val < count.val)
    (hcount : count.val ≤ 4)
    (hspan : start.val + count.val ≤ 19)
    (hpowers : KernelCanonicalQM31Array19 powers)
    (hvalues : KernelCanonicalQM31Array19 values)
    (hinvariant : KernelDotOuterInvariant current powers values
      start.val index.val) :
    ∃ next out,
      V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0.body
          powers values start count current index =
        .ok (.cont (out, next)) ∧
      next.val = index.val + 1 ∧
      KernelDotOuterInvariant out powers values start.val
        (index.val + 1) := by
  have harrayIndex : start.val + index.val < 19 := by omega
  have hcombined :
      (Std.Usize.wrapping_add start index).val = start.val + index.val :=
    kernel_usize_wrapping_add_val_below_nineteen start index harrayIndex
  let left : KernelQM31 := powers.val[start.val + index.val]!
  let right : KernelQM31 := values.val[start.val + index.val]!
  have hpowersIndex := kernel_generic_array_index_call powers
    (Std.Usize.wrapping_add start index) (by
    rw [hcombined]
    exact harrayIndex)
  have hvaluesIndex := kernel_generic_array_index_call values
    (Std.Usize.wrapping_add start index) (by
    rw [hcombined]
    exact harrayIndex)
  have hleft : KernelCanonicalQM31 left := by
    have h := hpowers ⟨start.val + index.val, harrayIndex⟩
    simpa [left, kernelArrayEntry] using h
  have hright : KernelCanonicalQM31 right := by
    have h := hvalues ⟨start.val + index.val, harrayIndex⟩
    simpa [right, kernelArrayEntry] using h
  have hspace : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (kernelMatrixCell current row channel).val +
        kernelChannelProductBound < kernelU64Cardinality := by
    intro row hrow channel hchannel
    have hcell := (hinvariant row hrow channel hchannel).1
    have hprocessed : index.val + 1 ≤ 4 := by omega
    calc
      (kernelMatrixCell current row channel).val +
          kernelChannelProductBound
          ≤ index.val * kernelChannelProductBound +
              kernelChannelProductBound :=
            Nat.add_le_add_right hcell _
      _ = (index.val + 1) * kernelChannelProductBound := by ring
      _ ≤ 4 * kernelChannelProductBound :=
        Nat.mul_le_mul_right kernelChannelProductBound hprocessed
      _ < kernelU64Cardinality := four_kernel_channel_products_fit_u64
  rcases extracted_dot_pair_channels_corresponds current left right
      hleft hright hspace with ⟨out, hpairRun, hpairPost⟩
  let next := Std.Usize.wrapping_add index 1#usize
  have hnext : next.val = index.val + 1 :=
    kernel_usize_wrapping_add_one_val index (by omega)
  have houtInvariant : KernelDotOuterInvariant out powers values start.val
      (index.val + 1) := by
    intro row hrow channel hchannel
    have hold := hinvariant row hrow channel hchannel
    have hstep := hpairPost row hrow channel hchannel
    constructor
    · exact le_trans hstep.1 (by
        calc
          (kernelMatrixCell current row channel).val +
              kernelChannelProductBound
              ≤ index.val * kernelChannelProductBound +
                  kernelChannelProductBound :=
                Nat.add_le_add_right hold.1 _
          _ = (index.val + 1) * kernelChannelProductBound := by ring)
    · rw [hstep.2, hold.2]
      simp [kernelExactChannelDotBlock, left, right,
        Finset.sum_range_succ]
  refine ⟨next, out, ?_, hnext, houtInvariant⟩
  unfold
    V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0.body
  simp only [show index < count from hactive, if_pos, Std.lift, bind_tc_ok]
  rw [hpowersIndex]
  simp only [bind_tc_ok, hcombined]
  rw [hvaluesIndex]
  simp only [bind_tc_ok, hcombined]
  have hpairRun' := hpairRun
  simp only [kernelGeneratedComponentMatrix] at hpairRun'
  have hwhole := congrArg
    (fun result : Result (Array (Array Std.U64 3#usize) 3#usize) =>
      result >>= fun sums1 =>
        .ok ((ControlFlow.cont
          (sums1, Std.Usize.wrapping_add index 1#usize)) :
            ControlFlow
              (Array (Array Std.U64 3#usize) 3#usize × Std.Usize)
              (Array (Array Std.U64 3#usize) 3#usize)))
    hpairRun'
  simpa only [bind_tc_ok, left, right, next, bind_assoc] using hwhole

private theorem kernel_dot_outer_body_done
    (powers values : Array KernelQM31 19#usize)
    (start count : Std.Usize)
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (index : Std.Usize) (hdone : ¬ index.val < count.val) :
    V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0.body
        powers values start count current index = .ok (.done current) := by
  unfold
    V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0.body
  simp [hdone]

theorem extracted_dot_outer_loop_corresponds
    (powers values : Array KernelQM31 19#usize)
    (start count : Std.Usize)
    (initial : Array (Array Std.U64 3#usize) 3#usize)
    (hcount : count.val ≤ 4)
    (hspan : start.val + count.val ≤ 19)
    (hpowers : KernelCanonicalQM31Array19 powers)
    (hvalues : KernelCanonicalQM31Array19 values)
    (hinitial : KernelDotOuterInvariant initial powers values start.val 0) :
    V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0
        powers values start count initial 0#usize
      ⦃ out => KernelDotOuterInvariant out powers values start.val count.val ⦄ := by
  simp only [V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0]
  apply loop.spec_decr_nat
    (fun state : Array (Array Std.U64 3#usize) 3#usize × Std.Usize =>
      count.val - state.2.val)
    (fun state => state.2.val ≤ count.val ∧
      KernelDotOuterInvariant state.1 powers values start.val state.2.val)
    (fun out => KernelDotOuterInvariant out powers values start.val count.val)
  · rintro ⟨current, index⟩ ⟨hindexLe, hinvariant⟩
    dsimp only at hindexLe hinvariant ⊢
    by_cases hactive : index.val < count.val
    · obtain ⟨next, out, hbody, hnext, hout⟩ :=
        kernel_dot_outer_body_active powers values start count current index
          hactive hcount hspan hpowers hvalues hinvariant
      rw [hbody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hnext]
        omega
      · rw [hnext]
        exact hout
      · rw [hnext]
        omega
    · have hatEnd : index.val = count.val := by omega
      rw [kernel_dot_outer_body_done powers values start count current index
        hactive]
      simpa [hatEnd] using hinvariant
  · exact ⟨by norm_num, hinitial⟩

private theorem kernel_P_eq_reduce_existing :
    V5RelationPreparedClaimsGenerated.aspis_core.field.P =
      aspis_core.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5RelationPreparedClaimsGenerated.aspis_core.field.P
    aspis_core.field.P
  rfl

private theorem kernel_reduce_u64_eq_reduce_existing (x : Std.U64) :
    V5RelationPreparedClaimsGenerated.aspis_core.field.reduce_u64 x =
      aspis_core.field.reduce_u64 x := by
  unfold V5RelationPreparedClaimsGenerated.aspis_core.field.reduce_u64
    aspis_core.field.reduce_u64
  rw [kernel_P_eq_reduce_existing]

private theorem kernel_m31_reduce_u64_corresponds (x : Std.U64) :
    ∃ out : KernelM31,
      V5RelationPreparedClaimsGenerated.aspis_core.field.M31.reduce_u64 x =
        .ok out ∧
      KernelCanonicalM31 out.val ∧
      ((out.val : Nat) : KernelM31Exact) = (x.val : KernelM31Exact) := by
  rcases AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds x with
    ⟨out, hout, _hraw, hcanonical, hexact⟩
  have hfresh :
      V5RelationPreparedClaimsGenerated.aspis_core.field.reduce_u64 x =
        .ok out := by
    rw [kernel_reduce_u64_eq_reduce_existing]
    exact hout
  exact ⟨out, by simpa
    [V5RelationPreparedClaimsGenerated.aspis_core.field.M31.reduce_u64,
      hfresh], hcanonical, hexact⟩

def kernelReconstructCMExact (row : Array Std.U64 3#usize) :
    KernelCM31Exact :=
  ⟨((kernelRowCell row 0).val : KernelM31Exact) -
      ((kernelRowCell row 1).val : KernelM31Exact),
    ((kernelRowCell row 2).val : KernelM31Exact) -
      ((kernelRowCell row 0).val : KernelM31Exact) -
      ((kernelRowCell row 1).val : KernelM31Exact)⟩

def kernelReconstructQMExact
    (sums : Array (Array Std.U64 3#usize) 3#usize) : KernelQM31Exact :=
  let m0 := kernelReconstructCMExact sums.val[0]!
  let m1 := kernelReconstructCMExact sums.val[1]!
  let m2 := kernelReconstructCMExact sums.val[2]!
  ⟨m0 + AspisAeneasQM31Mul.qm31R * m1, m2 - m0 - m1⟩

private theorem extracted_dot_reconstruct_closure_corresponds
    (channels : Array Std.U64 3#usize) :
    ∃ out : KernelCM31,
      V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
          () channels = .ok out ∧
      KernelCanonicalCM31 out ∧
      kernelCM31ToExact out = kernelReconstructCMExact channels := by
  have h0 := kernel_generic_array_index_call channels 0#usize (by norm_num)
  have h1 := kernel_generic_array_index_call channels 1#usize (by norm_num)
  have h2 := kernel_generic_array_index_call channels 2#usize (by norm_num)
  have hget0 : channels.val[0] = kernelRowCell channels 0 :=
    kernel_list_get_eq_getElemBang channels.val 0 (by simp)
  have hget1 : channels.val[1] = kernelRowCell channels 1 :=
    kernel_list_get_eq_getElemBang channels.val 1 (by simp)
  have hget2 : channels.val[2] = kernelRowCell channels 2 :=
    kernel_list_get_eq_getElemBang channels.val 2 (by simp)
  rcases kernel_m31_reduce_u64_corresponds (kernelRowCell channels 0) with
    ⟨m0, hm0, hm0Canonical, hm0Exact⟩
  rcases kernel_m31_reduce_u64_corresponds (kernelRowCell channels 1) with
    ⟨m1, hm1, hm1Canonical, hm1Exact⟩
  rcases kernel_m31_reduce_u64_corresponds (kernelRowCell channels 2) with
    ⟨m2, hm2, hm2Canonical, hm2Exact⟩
  rcases kernel_m31_sub_corresponds m0 m1 hm0Canonical hm1Canonical with
    ⟨real, hreal, hrealCanonical, hrealExact⟩
  rcases kernel_m31_sub_corresponds m2 m0 hm2Canonical hm0Canonical with
    ⟨imag0, himag0, himag0Canonical, himag0Exact⟩
  rcases kernel_m31_sub_corresponds imag0 m1
      himag0Canonical hm1Canonical with
    ⟨imag, himag, himagCanonical, himagExact⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · simp [V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call,
      h0, h1, h2, hget0, hget1, hget2,
      hm0, hm1, hm2, hreal, himag0, himag]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : KernelM31Exact) =
        ((kernelRowCell channels 0).val : KernelM31Exact) -
          ((kernelRowCell channels 1).val : KernelM31Exact)
      rw [hrealExact, hm0Exact, hm1Exact]
    · calc
        (kernelCM31ToExact ⟨real, imag⟩).im =
            ((imag.val : Nat) : KernelM31Exact) := rfl
        _ = ((imag0.val : Nat) : KernelM31Exact) -
              ((m1.val : Nat) : KernelM31Exact) := himagExact
        _ = (((m2.val : Nat) : KernelM31Exact) -
              ((m0.val : Nat) : KernelM31Exact)) -
              ((m1.val : Nat) : KernelM31Exact) := by rw [himag0Exact]
        _ = (kernelReconstructCMExact channels).im := by
          change _ = ((kernelRowCell channels 2).val : KernelM31Exact) -
            ((kernelRowCell channels 0).val : KernelM31Exact) -
            ((kernelRowCell channels 1).val : KernelM31Exact)
          rw [hm0Exact, hm1Exact, hm2Exact]

theorem extracted_dot_reconstruction_corresponds
    (sums : Array (Array Std.U64 3#usize) 3#usize) :
    ∃ out : KernelQM31,
      (do
        let row0 ← Array.index_usize sums 0#usize
        let m0 ←
          V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
            () row0
        let row1 ← Array.index_usize sums 1#usize
        let m1 ←
          V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
            () row1
        let row2 ← Array.index_usize sums 2#usize
        let m2 ←
          V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
            () row2
        let twoA ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.double m1.a
        let real ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.sub twoA m1.b
        let twoB ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.double m1.b
        let imag ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.add m1.a twoB
        let low ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.add m0
            { a := real, b := imag }
        let high0 ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.sub m2 m0
        let high ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.sub high0 m1
        ok ({ c0 := low, c1 := high } : KernelQM31)) = .ok out ∧
      KernelCanonicalQM31 out ∧
      kernelQM31ToExact out = kernelReconstructQMExact sums := by
  have hrow0 := kernel_generic_array_index_call sums 0#usize (by norm_num)
  have hrow1 := kernel_generic_array_index_call sums 1#usize (by norm_num)
  have hrow2 := kernel_generic_array_index_call sums 2#usize (by norm_num)
  rcases extracted_dot_reconstruct_closure_corresponds
      sums.val[(0#usize).val]! with
    ⟨m0, hm0, hm0Canonical, hm0Exact⟩
  rcases extracted_dot_reconstruct_closure_corresponds
      sums.val[(1#usize).val]! with
    ⟨m1, hm1, hm1Canonical, hm1Exact⟩
  rcases extracted_dot_reconstruct_closure_corresponds
      sums.val[(2#usize).val]! with
    ⟨m2, hm2, hm2Canonical, hm2Exact⟩
  rcases kernel_m31_double_corresponds m1.a hm1Canonical.1 with
    ⟨twoA, htwoA, htwoACanonical, htwoAExact⟩
  rcases kernel_m31_sub_corresponds twoA m1.b
      htwoACanonical hm1Canonical.2 with
    ⟨real, hreal, hrealCanonical, hrealExact⟩
  rcases kernel_m31_double_corresponds m1.b hm1Canonical.2 with
    ⟨twoB, htwoB, htwoBCanonical, htwoBExact⟩
  rcases kernel_m31_add_corresponds m1.a twoB
      hm1Canonical.1 htwoBCanonical with
    ⟨imag, himag, himagCanonical, himagExact⟩
  let rm1 : KernelCM31 := ⟨real, imag⟩
  have hrm1Canonical : KernelCanonicalCM31 rm1 :=
    ⟨hrealCanonical, himagCanonical⟩
  have hrm1Exact : kernelCM31ToExact rm1 =
      AspisAeneasQM31Mul.qm31R * kernelCM31ToExact m1 := by
    apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : KernelM31Exact) = _
      rw [hrealExact, htwoAExact]
      simp only [kernelCM31ToExact, AspisAeneasQM31Mul.qm31R,
        QuadraticAlgebra.re_mul]
      ring
    · change ((imag.val : Nat) : KernelM31Exact) = _
      rw [himagExact, htwoBExact]
      simp only [kernelCM31ToExact, AspisAeneasQM31Mul.qm31R,
        QuadraticAlgebra.im_mul]
      ring
  rcases kernel_cm31_add_corresponds m0 rm1 hm0Canonical hrm1Canonical with
    ⟨low, hlow, hlowCanonical, hlowExact⟩
  rcases kernel_cm31_sub_corresponds m2 m0 hm2Canonical hm0Canonical with
    ⟨high0, hhigh0, hhigh0Canonical, hhigh0Exact⟩
  rcases kernel_cm31_sub_corresponds high0 m1
      hhigh0Canonical hm1Canonical with
    ⟨high, hhigh, hhighCanonical, hhighExact⟩
  refine ⟨⟨low, high⟩, ?_, ⟨hlowCanonical, hhighCanonical⟩, ?_⟩
  · rw [hrow0]
    simp only [bind_tc_ok]
    rw [hm0, hrow1]
    simp only [bind_tc_ok]
    rw [hm1, hrow2]
    simp only [bind_tc_ok]
    rw [hm2]
    simp only [bind_tc_ok]
    rw [htwoA]
    simp only [bind_tc_ok]
    rw [hreal]
    simp only [bind_tc_ok]
    rw [htwoB]
    simp only [bind_tc_ok]
    rw [himag]
    simp only [bind_tc_ok]
    change (do
      let low1 ←
        V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.add m0 rm1
      let high01 ←
        V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.sub m2 m0
      let high1 ←
        V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.sub high01 m1
      ok ({ c0 := low1, c1 := high1 } : KernelQM31)) = _
    rw [hlow]
    simp only [bind_tc_ok]
    rw [hhigh0]
    simp only [bind_tc_ok]
    rw [hhigh]
    simp only [bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · change kernelCM31ToExact low = _
      rw [hlowExact, hrm1Exact, hm0Exact, hm1Exact]
      rfl
    · change kernelCM31ToExact high = _
      rw [hhighExact, hhigh0Exact, hm0Exact, hm1Exact, hm2Exact]
      rfl

def kernelZeroU64ChannelMatrix :
    Array (Array Std.U64 3#usize) 3#usize :=
  Array.repeat 3#usize (Array.repeat 3#usize 0#u64)

private theorem kernel_zero_u64_channel_cell
    (row channel : Nat) (hrow : row < 3) (hchannel : channel < 3) :
    kernelMatrixCell kernelZeroU64ChannelMatrix row channel = 0#u64 := by
  have hrow' : row < (3#usize).val := by simpa using hrow
  have hchannel' : channel < (3#usize).val := by simpa using hchannel
  unfold kernelMatrixCell kernelRowCell kernelZeroU64ChannelMatrix
  rw [Array.repeat_val, List.getElem!_replicate _ hrow']
  rw [Array.repeat_val, List.getElem!_replicate _ hchannel']

theorem kernel_zero_dot_outer_invariant
    (powers values : Array KernelQM31 19#usize) (start : Nat) :
    KernelDotOuterInvariant kernelZeroU64ChannelMatrix powers values start 0 := by
  intro row hrow channel hchannel
  rw [kernel_zero_u64_channel_cell row channel hrow hchannel]
  simp [kernelExactChannelDotBlock]

def kernelReconstructExactChannels
    (channels : Nat → Nat → KernelM31Exact) : KernelQM31Exact :=
  let component := fun row =>
    (⟨channels row 0 - channels row 1,
      channels row 2 - channels row 0 - channels row 1⟩ : KernelCM31Exact)
  let m0 := component 0
  let m1 := component 1
  let m2 := component 2
  ⟨m0 + AspisAeneasQM31Mul.qm31R * m1, m2 - m0 - m1⟩

private theorem kernel_reconstruct_exact_channels_add
    (f g : Nat → Nat → KernelM31Exact) :
    kernelReconstructExactChannels (fun row channel =>
      f row channel + g row channel) =
      kernelReconstructExactChannels f + kernelReconstructExactChannels g := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_add]
      simp [kernelReconstructExactChannels, AspisAeneasQM31Mul.qm31R]
      ring
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
      simp [kernelReconstructExactChannels, AspisAeneasQM31Mul.qm31R]
      ring
  · apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.re_add]
      simp [kernelReconstructExactChannels, AspisAeneasQM31Mul.qm31R]
      ring
    · simp only [QuadraticAlgebra.im_add]
      simp [kernelReconstructExactChannels, AspisAeneasQM31Mul.qm31R]
      ring

private theorem kernel_reconstruct_exact_channels_zero :
    kernelReconstructExactChannels (fun _ _ => 0) = 0 := by
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    simp [kernelReconstructExactChannels, AspisAeneasQM31Mul.qm31R]

private theorem kernel_reconstruct_exact_channels_finset_sum
    (s : Finset Nat) (f : Nat → Nat → Nat → KernelM31Exact) :
    kernelReconstructExactChannels (fun row channel =>
      ∑ index ∈ s, f index row channel) =
      ∑ index ∈ s, kernelReconstructExactChannels (f index) := by
  induction s using Finset.induction_on with
  | empty => simpa using kernel_reconstruct_exact_channels_zero
  | @insert index s hfresh ih =>
      simp only [Finset.sum_insert hfresh]
      rw [kernel_reconstruct_exact_channels_add, ih]

private theorem kernel_reconstruct_single_product_eq_mul
    (left right : KernelQM31) :
    kernelReconstructExactChannels (fun row channel =>
      kernelExactInputChannel left row channel *
        kernelExactInputChannel right row channel) =
      kernelQM31ToExact left * kernelQM31ToExact right := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul]
      simp [kernelReconstructExactChannels, kernelExactInputChannel,
        kernelExactQMComponent, kernelExactCMChannel, kernelQM31ToExact,
        kernelCM31ToExact, AspisAeneasQM31Mul.qm31R]
      ring
    · simp only [QuadraticAlgebra.re_mul]
      simp [kernelReconstructExactChannels, kernelExactInputChannel,
        kernelExactQMComponent, kernelExactCMChannel, kernelQM31ToExact,
        kernelCM31ToExact, AspisAeneasQM31Mul.qm31R]
      ring
  · apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.im_mul]
      simp [kernelReconstructExactChannels, kernelExactInputChannel,
        kernelExactQMComponent, kernelExactCMChannel, kernelQM31ToExact,
        kernelCM31ToExact, AspisAeneasQM31Mul.qm31R]
      ring
    · simp only [QuadraticAlgebra.im_mul]
      simp [kernelReconstructExactChannels, kernelExactInputChannel,
        kernelExactQMComponent, kernelExactCMChannel, kernelQM31ToExact,
        kernelCM31ToExact, AspisAeneasQM31Mul.qm31R]
      ring

def kernelExactBlockDot
    (powers values : Array KernelQM31 19#usize)
    (start count : Nat) : KernelQM31Exact :=
  ∑ offset ∈ Finset.range count,
    kernelQM31ToExact powers.val[start + offset]! *
      kernelQM31ToExact values.val[start + offset]!

private theorem kernel_reconstruct_exact_channels_block_eq_dot
    (powers values : Array KernelQM31 19#usize)
    (start count : Nat) :
    kernelReconstructExactChannels (fun row channel =>
      kernelExactChannelDotBlock powers values start count row channel) =
      kernelExactBlockDot powers values start count := by
  unfold kernelExactChannelDotBlock kernelExactBlockDot
  rw [kernel_reconstruct_exact_channels_finset_sum]
  apply Finset.sum_congr rfl
  intro index hindex
  exact kernel_reconstruct_single_product_eq_mul
    powers.val[start + index]! values.val[start + index]!

private theorem kernel_reconstruct_qm_exact_eq_block_dot
    (powers values : Array KernelQM31 19#usize)
    (start count : Nat)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (hchannels : KernelDotOuterInvariant sums powers values start count) :
    kernelReconstructQMExact sums =
      kernelExactBlockDot powers values start count := by
  have h00 := (hchannels 0 (by omega) 0 (by omega)).2
  have h01 := (hchannels 0 (by omega) 1 (by omega)).2
  have h02 := (hchannels 0 (by omega) 2 (by omega)).2
  have h10 := (hchannels 1 (by omega) 0 (by omega)).2
  have h11 := (hchannels 1 (by omega) 1 (by omega)).2
  have h12 := (hchannels 1 (by omega) 2 (by omega)).2
  have h20 := (hchannels 2 (by omega) 0 (by omega)).2
  have h21 := (hchannels 2 (by omega) 1 (by omega)).2
  have h22 := (hchannels 2 (by omega) 2 (by omega)).2
  unfold kernelMatrixCell at h00 h01 h02 h10 h11 h12 h20 h21 h22
  norm_num at h00 h01 h02 h10 h11 h12 h20 h21 h22
  rw [← kernel_reconstruct_exact_channels_block_eq_dot powers values
    start count]
  unfold kernelReconstructQMExact kernelReconstructCMExact
    kernelReconstructExactChannels
  norm_num
  rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  constructor
  · rfl
  · constructor <;> rfl

/-- Universal exact correspondence for the generated production block helper.
The domain is precisely the production one: at most four consecutive entries
inside the nineteen-entry table, with canonical field encodings. -/
theorem extracted_claim_dot_block_corresponds
    (powers values : Array KernelQM31 19#usize)
    (start count : Std.Usize)
    (hcount : count.val ≤ 4)
    (hspan : start.val + count.val ≤ 19)
    (hpowers : KernelCanonicalQM31Array19 powers)
    (hvalues : KernelCanonicalQM31Array19 values) :
    ∃ out : KernelQM31,
      V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block
          powers values start count = .ok out ∧
      KernelCanonicalQM31 out ∧
      kernelQM31ToExact out =
        kernelExactBlockDot powers values start.val count.val := by
  have houterSpec := extracted_dot_outer_loop_corresponds powers values
    start count kernelZeroU64ChannelMatrix hcount hspan hpowers hvalues
    (kernel_zero_dot_outer_invariant powers values start.val)
  obtain ⟨sums, houterRun, hchannels⟩ :=
    Aeneas.Std.WP.spec_imp_exists houterSpec
  rcases extracted_dot_reconstruction_corresponds sums with
    ⟨out, hreconstruct, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, ?_⟩
  · unfold V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block
    change
      (do
        let sums1 ←
          V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block_loop0
            powers values start count kernelZeroU64ChannelMatrix 0#usize
        let row0 ← Array.index_usize sums1 0#usize
        let m0 ←
          V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
            () row0
        let row1 ← Array.index_usize sums1 1#usize
        let m1 ←
          V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
            () row1
        let row2 ← Array.index_usize sums1 2#usize
        let m2 ←
          V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
            () row2
        let twoA ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.double m1.a
        let real ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.sub twoA m1.b
        let twoB ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.double m1.b
        let imag ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.M31.add m1.a twoB
        let low ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.add m0
            { a := real, b := imag }
        let high0 ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.sub m2 m0
        let high ←
          V5RelationPreparedClaimsGenerated.aspis_core.field.CM31.sub high0 m1
        ok ({ c0 := low, c1 := high } : KernelQM31)) = .ok out
    rw [houterRun]
    simp only [bind_tc_ok]
    exact hreconstruct
  · rw [hexact]
    exact kernel_reconstruct_qm_exact_eq_block_dot powers values
      start.val count.val sums hchannels

/-! This definitional trace theorem remains useful when inspecting a fresh
extraction.  The stronger universal mathematical result is
`extracted_gamma_powers_eq_source_weights` above. -/

theorem extracted_gamma_builder_enters_at_exponent_two
    (gamma : V5RelationPreparedClaimsGenerated.aspis_core.field.QM31) :
    V5RelationPreparedClaimsGenerated.fri_checks.v5_gamma_powers gamma = (do
      let powers := Aeneas.Std.Array.repeat 19#usize
        V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ZERO
      let powers ← Aeneas.Std.Array.update powers 0#usize
        V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.ONE
      let powers ← Aeneas.Std.Array.update powers 1#usize gamma
      V5RelationPreparedClaimsGenerated.fri_checks.v5_gamma_powers_loop
        gamma powers 2#usize) := by
  rfl

#print axioms extracted_kernel_qm31_mul_corresponds
#print axioms extracted_kernel_qm31_square_corresponds
#print axioms extracted_gamma_powers_eq_source_weights
#print axioms extracted_dot_channel_loop_corresponds
#print axioms extracted_dot_component_loop_corresponds
#print axioms extracted_dot_outer_loop_corresponds
#print axioms extracted_dot_reconstruction_corresponds
#print axioms extracted_claim_dot_block_corresponds
#print axioms extracted_gamma_builder_enters_at_exponent_two

end AspisV5PreparedPointClaimsSourceProof
