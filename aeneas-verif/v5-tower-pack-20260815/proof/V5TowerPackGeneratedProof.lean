import V5TowerPack.Funs
import M31ReduceU64Proof
import AspisFormal.V5ExactTowerPacking

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5TowerPackGeneratedProof

open V5TowerPackGenerated

abbrev RawM31 := V5TowerPackGenerated.field.M31
abbrev RawQM31 := V5TowerPackGenerated.field.QM31

def baseLift (x : RawM31) : RawQM31 :=
  { c0 := { a := x, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

def baseFourSlice (x0 x1 x2 x3 : RawM31) : Slice RawQM31 :=
  Array.to_slice (Array.make 4#usize
    [baseLift x0, baseLift x1, baseLift x2, baseLift x3])

def expectedPack (x0 x1 x2 x3 : RawM31) : RawQM31 :=
  { c0 := { a := x0, b := x1 }, c1 := { a := x2, b := x3 } }

theorem generated_reduce_eq_existing (x : Std.U64) :
    V5TowerPackGenerated.field.reduce_u64 x =
      aspis_core.field.reduce_u64 x := by
  simp [V5TowerPackGenerated.field.reduce_u64,
    V5TowerPackGenerated.field.P,
    aspis_core.field.reduce_u64, aspis_core.field.P, Std.lift]

abbrev P : Nat := 2147483647
abbrev M31Exact := ZMod P

theorem generated_m31_reduce_u64_corresponds (x : Std.U64) :
    ∃ out : RawM31,
      V5TowerPackGenerated.field.M31.reduce_u64 x = .ok out ∧
      out.val < P ∧
      ((out.val : Nat) : M31Exact) = (x.val : M31Exact) := by
  rcases AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds x with
    ⟨out, hcall, _hraw, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  unfold V5TowerPackGenerated.field.M31.reduce_u64
  rw [generated_reduce_eq_existing, hcall]
  rfl

theorem canonical_raw_eq_of_residue_eq
    (left right : Nat) (hleft : left < P) (hright : right < P)
    (equal : (left : M31Exact) = (right : M31Exact)) :
    left = right := by
  have values := congrArg ZMod.val equal
  simpa [ZMod.val_natCast_of_lt hleft, ZMod.val_natCast_of_lt hright]
    using values

def liftM31 (x : RawM31) : Std.U64 :=
  core.convert.num.FromU64U32.from x

def p64 : Std.U64 := liftM31 2147483647#u32
def z64 : Std.U64 := liftM31 0#u32

def packedAccumulator0 (x : RawM31) : Std.U64 :=
  (((((liftM31 x).wrapping_add (p64.wrapping_sub z64)).wrapping_add
          (Std.U64.wrapping_mul 2#u64 z64)).wrapping_add
        (p64.wrapping_sub z64)).wrapping_add
      (p64.wrapping_sub z64)).wrapping_add
    ((Std.U64.wrapping_mul 2#u64 p64).wrapping_sub
      (Std.U64.wrapping_mul 2#u64 z64))

def packedAccumulator1 (x : RawM31) : Std.U64 :=
  (((((z64.wrapping_add (liftM31 x)).wrapping_add z64).wrapping_add
          (Std.U64.wrapping_mul 2#u64 z64)).wrapping_add
        (Std.U64.wrapping_mul 2#u64 z64)).wrapping_add
      (p64.wrapping_sub z64))

def packedAccumulator2 (x : RawM31) : Std.U64 :=
  (((z64.wrapping_add (p64.wrapping_sub z64)).wrapping_add
      (liftM31 x)).wrapping_add (p64.wrapping_sub z64))

def packedAccumulator3 (x : RawM31) : Std.U64 :=
  (((z64.wrapping_add z64).wrapping_add z64).wrapping_add (liftM31 x))

@[simp]
theorem liftM31_val (x : RawM31) : (liftM31 x).val = x.val := by
  simp [liftM31, core.convert.num.FromU64U32.from_val_eq]

theorem u64_wrapping_add_exact (left right : Std.U64)
    (bound : left.val + right.val < Std.U64.size) :
    (left.wrapping_add right).val = left.val + right.val := by
  rw [Std.U64.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [U64.size, U64.numBits, UScalarTy.U64_numBits_eq] using bound

@[simp]
theorem p64_sub_z64_val : (p64.wrapping_sub z64).val = P := by
  norm_num [p64, z64, liftM31, Std.U64.wrapping_sub_val_eq,
    U64.size, U64.numBits, UScalarTy.U64_numBits_eq, P]

@[simp]
theorem two_z64_val : (Std.U64.wrapping_mul 2#u64 z64).val = 0 := by
  norm_num [z64, liftM31, Std.U64.wrapping_mul_val_eq,
    U64.size, U64.numBits, UScalarTy.U64_numBits_eq]

@[simp]
theorem packedAccumulator0_tail_val :
    ((Std.U64.wrapping_mul 2#u64 p64).wrapping_sub
      (Std.U64.wrapping_mul 2#u64 z64)).val = 2 * P := by
  norm_num [p64, z64, liftM31, Std.U64.wrapping_mul_val_eq,
    Std.U64.wrapping_sub_val_eq, U64.size, U64.numBits,
    UScalarTy.U64_numBits_eq, P]

theorem generated_pack_base4_decomposes
    (x0 x1 x2 x3 : RawM31) :
    V5TowerPackGenerated.field.qm31_pack_base4
        (baseFourSlice x0 x1 x2 x3) = (do
      let m0 ← V5TowerPackGenerated.field.M31.reduce_u64
        (packedAccumulator0 x0)
      let m1 ← V5TowerPackGenerated.field.M31.reduce_u64
        (packedAccumulator1 x1)
      let m2 ← V5TowerPackGenerated.field.M31.reduce_u64
        (packedAccumulator2 x2)
      let m3 ← V5TowerPackGenerated.field.M31.reduce_u64
        (packedAccumulator3 x3)
      ok { c0 := { a := m0, b := m1 }, c1 := { a := m2, b := m3 } }) := by
  simp [V5TowerPackGenerated.field.qm31_pack_base4,
    baseFourSlice, baseLift, packedAccumulator0, packedAccumulator1,
    packedAccumulator2, packedAccumulator3, liftM31, p64, z64,
    V5TowerPackGenerated.field.QM31.ZERO,
    V5TowerPackGenerated.field.P,
    V5TowerPackGenerated.field.CM31.new, Std.lift,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    Array.index_usize, Array.make, Slice.len, Slice.length,
    V5TowerPackGenerated.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call]
  simp_lists
  simp

theorem packedAccumulator0_val (x : RawM31) (hx : x.val < P) :
    (packedAccumulator0 x).val = x.val + 5 * P := by
  let step1 := (liftM31 x).wrapping_add (p64.wrapping_sub z64)
  let step2 := step1.wrapping_add (Std.U64.wrapping_mul 2#u64 z64)
  let step3 := step2.wrapping_add (p64.wrapping_sub z64)
  let step4 := step3.wrapping_add (p64.wrapping_sub z64)
  let tail := (Std.U64.wrapping_mul 2#u64 p64).wrapping_sub
    (Std.U64.wrapping_mul 2#u64 z64)
  change (step4.wrapping_add tail).val = x.val + 5 * P
  have step1Bound :
      (liftM31 x).val + (p64.wrapping_sub z64).val < Std.U64.size := by
    rw [liftM31_val, p64_sub_z64_val]
    norm_num [P, U64.size, U64.numBits, UScalarTy.U64_numBits_eq] at hx ⊢
    omega
  have step1Value : step1.val = x.val + P := by
    rw [u64_wrapping_add_exact _ _ step1Bound, liftM31_val,
      p64_sub_z64_val]
  have step2Bound :
      step1.val + (Std.U64.wrapping_mul 2#u64 z64).val < Std.U64.size := by
    rw [step1Value, two_z64_val]
    norm_num [P, U64.size, U64.numBits, UScalarTy.U64_numBits_eq] at hx ⊢
    omega
  have step2Value : step2.val = x.val + P := by
    rw [u64_wrapping_add_exact _ _ step2Bound, step1Value, two_z64_val,
      Nat.add_zero]
  have step3Bound :
      step2.val + (p64.wrapping_sub z64).val < Std.U64.size := by
    rw [step2Value, p64_sub_z64_val]
    norm_num [P, U64.size, U64.numBits, UScalarTy.U64_numBits_eq] at hx ⊢
    omega
  have step3Value : step3.val = x.val + 2 * P := by
    rw [u64_wrapping_add_exact _ _ step3Bound, step2Value,
      p64_sub_z64_val]
    omega
  have step4Bound :
      step3.val + (p64.wrapping_sub z64).val < Std.U64.size := by
    rw [step3Value, p64_sub_z64_val]
    norm_num [P, U64.size, U64.numBits, UScalarTy.U64_numBits_eq] at hx ⊢
    omega
  have step4Value : step4.val = x.val + 3 * P := by
    rw [u64_wrapping_add_exact _ _ step4Bound, step3Value,
      p64_sub_z64_val]
    omega
  have finalBound : step4.val + tail.val < Std.U64.size := by
    rw [step4Value, packedAccumulator0_tail_val]
    norm_num [P, U64.size, U64.numBits, UScalarTy.U64_numBits_eq] at hx ⊢
    omega
  rw [u64_wrapping_add_exact _ _ finalBound, step4Value,
    packedAccumulator0_tail_val]
  omega

theorem packedAccumulator1_val (x : RawM31) (hx : x.val < P) :
    (packedAccumulator1 x).val = x.val + P := by
  have hxSize := UScalar.hSize x
  norm_num [P] at hx
  simp [U32.size, U32.numBits] at hxSize
  simp [packedAccumulator1, liftM31, p64, z64,
    Std.U64.wrapping_add_val_eq, Std.U64.wrapping_sub_val_eq,
    Std.U64.wrapping_mul_val_eq, U64.size, U64.numBits,
    UScalarTy.U64_numBits_eq, P]
  omega

theorem packedAccumulator2_val (x : RawM31) (hx : x.val < P) :
    (packedAccumulator2 x).val = x.val + 2 * P := by
  have hxSize := UScalar.hSize x
  norm_num [P] at hx
  simp [U32.size, U32.numBits] at hxSize
  simp [packedAccumulator2, liftM31, p64, z64,
    Std.U64.wrapping_add_val_eq, Std.U64.wrapping_sub_val_eq,
    U64.size, U64.numBits, UScalarTy.U64_numBits_eq, P]
  omega

theorem packedAccumulator3_val (x : RawM31) :
    (packedAccumulator3 x).val = x.val := by
  have hxSize := UScalar.hSize x
  simp [U32.size, U32.numBits] at hxSize
  simp [packedAccumulator3, liftM31, z64,
    Std.U64.wrapping_add_val_eq, U64.size, U64.numBits,
    UScalarTy.U64_numBits_eq]
  omega

theorem generated_pack_base4_on_base_values
    (x0 x1 x2 x3 : RawM31)
    (h0 : x0.val < P) (h1 : x1.val < P)
    (h2 : x2.val < P) (h3 : x3.val < P) :
    V5TowerPackGenerated.field.qm31_pack_base4
        (baseFourSlice x0 x1 x2 x3) =
      .ok (expectedPack x0 x1 x2 x3) := by
  rcases generated_m31_reduce_u64_corresponds (packedAccumulator0 x0) with
    ⟨o0, ho0, hcan0, hres0⟩
  rcases generated_m31_reduce_u64_corresponds (packedAccumulator1 x1) with
    ⟨o1, ho1, hcan1, hres1⟩
  rcases generated_m31_reduce_u64_corresponds (packedAccumulator2 x2) with
    ⟨o2, ho2, hcan2, hres2⟩
  rcases generated_m31_reduce_u64_corresponds (packedAccumulator3 x3) with
    ⟨o3, ho3, hcan3, hres3⟩
  have hacc0 : ((packedAccumulator0 x0).val : M31Exact) =
      (x0.val : M31Exact) := by
    rw [packedAccumulator0_val x0 h0]
    simp [P]
  have hacc1 : ((packedAccumulator1 x1).val : M31Exact) =
      (x1.val : M31Exact) := by
    rw [packedAccumulator1_val x1 h1]
    simp [P]
  have hacc2 : ((packedAccumulator2 x2).val : M31Exact) =
      (x2.val : M31Exact) := by
    rw [packedAccumulator2_val x2 h2]
    simp [P]
  have hacc3 : ((packedAccumulator3 x3).val : M31Exact) =
      (x3.val : M31Exact) := by
    rw [packedAccumulator3_val x3]
  have heq0 : o0 = x0 := by
    apply UScalar.eq_of_val_eq
    exact canonical_raw_eq_of_residue_eq o0.val x0.val hcan0 h0
      (hres0.trans hacc0)
  have heq1 : o1 = x1 := by
    apply UScalar.eq_of_val_eq
    exact canonical_raw_eq_of_residue_eq o1.val x1.val hcan1 h1
      (hres1.trans hacc1)
  have heq2 : o2 = x2 := by
    apply UScalar.eq_of_val_eq
    exact canonical_raw_eq_of_residue_eq o2.val x2.val hcan2 h2
      (hres2.trans hacc2)
  have heq3 : o3 = x3 := by
    apply UScalar.eq_of_val_eq
    exact canonical_raw_eq_of_residue_eq o3.val x3.val hcan3 h3
      (hres3.trans hacc3)
  rw [generated_pack_base4_decomposes, ho0, ho1, ho2, ho3]
  simp [heq0, heq1, heq2, heq3, expectedPack]

/-! ## Connection to the exact deployed tower basis -/

/-- Interpret the four raw Rust fields as their canonical M31 residues in the
exact mathematical QM31 tower. -/
def rawQM31ToExact (value : RawQM31) :
    AspisV5ComponentCQM31TowerExact.QM31Exact :=
  ⟨⟨value.c0.a.val, value.c0.b.val⟩,
   ⟨value.c1.a.val, value.c1.b.val⟩⟩

/-- The same four canonical residues as a coordinate vector. -/
def rawBaseCoordinates (x0 x1 x2 x3 : RawM31) :
    Fin 4 → AspisV5ComponentCQM31TowerExact.M31Exact :=
  ![(x0.val : M31Exact), (x1.val : M31Exact),
    (x2.val : M31Exact), (x3.val : M31Exact)]

/-- The expected raw Rust record is exactly packing in the deployed
`(1,i,u,i*u)` basis, rather than merely an unrelated four-field record. -/
theorem expectedPack_matches_deployedTowerBasis
    (x0 x1 x2 x3 : RawM31) :
    rawQM31ToExact (expectedPack x0 x1 x2 x3) =
      AspisV5TowerPackedResidualExtraction.towerPack
        AspisV5ExactTowerPacking.deployedTowerBasis
        (rawBaseCoordinates x0 x1 x2 x3) := by
  rw [AspisV5ExactTowerPacking.towerPack_deployedTowerBasis]
  rfl

/-- Universal release-code correspondence: for every four canonical M31 raw
inputs, successful execution of the extracted release Rust packer returns an
element whose exact tower interpretation is the deployed basis pack. -/
theorem generated_pack_base4_matches_deployedTowerBasis
    (x0 x1 x2 x3 : RawM31)
    (h0 : x0.val < P) (h1 : x1.val < P)
    (h2 : x2.val < P) (h3 : x3.val < P) :
    ∃ out : RawQM31,
      V5TowerPackGenerated.field.qm31_pack_base4
          (baseFourSlice x0 x1 x2 x3) = .ok out ∧
      rawQM31ToExact out =
        AspisV5TowerPackedResidualExtraction.towerPack
          AspisV5ExactTowerPacking.deployedTowerBasis
          (rawBaseCoordinates x0 x1 x2 x3) := by
  refine ⟨expectedPack x0 x1 x2 x3,
    generated_pack_base4_on_base_values x0 x1 x2 x3 h0 h1 h2 h3, ?_⟩
  exact expectedPack_matches_deployedTowerBasis x0 x1 x2 x3

#print axioms generated_reduce_eq_existing
#print axioms generated_m31_reduce_u64_corresponds
#print axioms canonical_raw_eq_of_residue_eq
#print axioms generated_pack_base4_decomposes
#print axioms packedAccumulator0_val
#print axioms generated_pack_base4_on_base_values
#print axioms expectedPack_matches_deployedTowerBasis
#print axioms generated_pack_base4_matches_deployedTowerBasis

end AspisV5TowerPackGeneratedProof
