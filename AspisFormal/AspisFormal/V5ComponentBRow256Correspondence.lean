import AspisFormal.V5ComponentBSpendDifferenceCoverage

/-!
# Component B row-256 encoder correspondence

This file narrows the row-256 deployment seam without changing the masking
construction.  The previous interface asked for the complete converted
128-coordinate raw map as one premise.  Here it is decomposed into exactly the
two executable facts that Rust semantics must provide:

* the width-64 ordinary-to-natural conversion used by the current host code;
* the 128 natural-basis rows at the 72 query/slot openings.

All algebra below those facts is kernel checked.  In particular, the natural
basis rows, the two independent width-64 conversions, physical p/q
interleaving, and the fixed runtime slot permutation imply the full universal
ordinary-basis matrix equality.  No fixture or numeric KAT is used.
-/

namespace AspisV5ComponentBRow256Correspondence

open Matrix
open AspisCircleTensorBinding
open AspisCircleRectangularMasking
open AspisCircleDiscreteAvailability
open AspisV5ComponentBCorrelatedResidualCoverage
open AspisV5ComponentBSpendDifferenceCoverage

abbrev Message := AspisV5ComponentBSpendDifferenceCoverage.Message
abbrev RawView := AspisV5ComponentBSpendDifferenceCoverage.RawView
abbrev RawCoordinate := AspisV5ComponentBSpendDifferenceCoverage.RawCoordinate
abbrev MLECoordinate := AspisV5ComponentBSpendDifferenceCoverage.MLECoordinate
abbrev FibreIndex := AspisV5ComponentBSpendDifferenceCoverage.FibreIndex
abbrev DeployedField := AspisV5ComponentBSpendDifferenceCoverage.DeployedField

section Algebra

variable {K : Type*} [Field K] [Algebra DeployedField K]

private theorem two_ne_zero_of_deployed_algebra : (2 : K) ≠ 0 := by
  have hbase : (2 : DeployedField) ≠ 0 := by
    have h : ((2 : ℕ) : DeployedField) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      decide
    simpa using h
  rw [← map_ofNat (algebraMap DeployedField K),
    ← map_zero (algebraMap DeployedField K)]
  exact (FaithfulSMul.algebraMap_injective DeployedField K).ne hbase

/-- The x-coordinate used by one raw query/slot, after the exact runtime slot
permutation and scalar extension to the verifier field. -/
def row256RawX
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (raw : RawCoordinate) : K :=
  algebraMap DeployedField K
    (signedCoordinate (rawToFibreIndex raw).2.1
      (representativeX (representativeQueries raw.1)))

/-- The corresponding signed y-coordinate. -/
def row256RawY
    (representativeQueries : Fin queryCount → Fin fibreCount)
    (raw : RawCoordinate) : K :=
  algebraMap DeployedField K
    (signedCoordinate (rawToFibreIndex raw).2.2
      (representativeY (representativeQueries raw.1)))

/-- The exact row-256 encoder factor selected by stored q18 and runtime slot. -/
def row256RawWeight
    (storedQueries : Fin queryCount → Fin fibreCount)
    (raw : RawCoordinate) : K :=
  algebraMap DeployedField K
    (row256ModelWeight storedQueries (rawToFibreIndex raw))

/-- Natural-line evaluation of the even physical rows 256,258,...,382. -/
noncomputable def row256NaturalPMatrix
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    Matrix RawCoordinate (Fin 64) K :=
  fun raw natural ↦
    row256RawWeight (K := K) storedQueries raw *
      (naturalLinePoly K natural).eval
        (row256RawX representativeQueries raw)

/-- Natural-line evaluation of the odd physical rows 257,259,...,383. -/
noncomputable def row256NaturalQMatrix
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    Matrix RawCoordinate (Fin 64) K :=
  fun raw natural ↦
    row256RawWeight (K := K) storedQueries raw *
      row256RawY representativeQueries raw *
        (naturalLinePoly K natural).eval
          (row256RawX representativeQueries raw)

/-- Read even physical offsets as the p natural-coordinate block. -/
def row256PhysicalPRead :
    (Fin 128 → K) →ₗ[K] (Fin 64 → K) :=
  LinearMap.pi fun index ↦ LinearMap.proj (row256PhysicalP index)

/-- Read odd physical offsets as the q natural-coordinate block. -/
def row256PhysicalQRead :
    (Fin 128 → K) →ₗ[K] (Fin 64 → K) :=
  LinearMap.pi fun index ↦ LinearMap.proj (row256PhysicalQ index)

/-- The full 128-natural-row encoder model in query-major/runtime-slot order.
It is deliberately expressed as two 64-wide natural-line evaluations so the
existing conversion theorem applies directly. -/
noncomputable def row256NaturalPhysicalRawMap
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    (Fin 128 → K) →ₗ[K] RawView K :=
  ((row256NaturalPMatrix (K := K) storedQueries representativeQueries).mulVecLin.comp
      row256PhysicalPRead) +
    ((row256NaturalQMatrix (K := K) storedQueries representativeQueries).mulVecLin.comp
      row256PhysicalQRead)

omit [Algebra DeployedField K] in
@[simp] theorem row256PhysicalPRead_after_conversion
    (ordinary : Fin 128 → K) :
    row256PhysicalPRead
        (row256OrdinaryToInterleavedNatural K ordinary) =
      (monomialToNatural K 64).mulVec (row256OrdinaryP ordinary) := by
  funext index
  exact row256OrdinaryToInterleavedNatural_at_p ordinary index

omit [Algebra DeployedField K] in
@[simp] theorem row256PhysicalQRead_after_conversion
    (ordinary : Fin 128 → K) :
    row256PhysicalQRead
        (row256OrdinaryToInterleavedNatural K ordinary) =
      (monomialToNatural K 64).mulVec (row256OrdinaryQ ordinary) := by
  funext index
  exact row256OrdinaryToInterleavedNatural_at_q ordinary index

theorem row256NaturalPMatrix_mul_conversion
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    row256NaturalPMatrix (K := K) storedQueries representativeQueries *
        monomialToNatural K 64 =
      fun raw (degree : Fin 64) ↦
        row256RawWeight (K := K) storedQueries raw *
          row256RawX representativeQueries raw ^ (degree : ℕ) := by
  classical
  letI : NeZero (2 : K) := ⟨two_ne_zero_of_deployed_algebra⟩
  ext raw degree
  have hbase := congrArg (fun matrix ↦ matrix (0 : Fin 1) degree)
    (naturalEval_mul_monomialToNatural_rect
      (K := K) (m := 64)
      (fun _ : Fin 1 ↦ row256RawX representativeQueries raw))
  simp only [Matrix.mul_apply, naturalEvalMatrix, monomialEvalMatrix] at hbase
  rw [Matrix.mul_apply]
  simp only [row256NaturalPMatrix]
  calc
    (∑ natural : Fin 64,
        row256RawWeight (K := K) storedQueries raw *
            (naturalLinePoly K natural).eval
              (row256RawX representativeQueries raw) *
          monomialToNatural K 64 natural degree) =
        row256RawWeight (K := K) storedQueries raw *
          ∑ natural : Fin 64,
            (naturalLinePoly K natural).eval
                (row256RawX representativeQueries raw) *
              monomialToNatural K 64 natural degree := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro natural _
      ring
    _ = _ := by rw [hbase]

theorem row256NaturalQMatrix_mul_conversion
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    row256NaturalQMatrix (K := K) storedQueries representativeQueries *
        monomialToNatural K 64 =
      fun raw (degree : Fin 64) ↦
        row256RawWeight (K := K) storedQueries raw *
          row256RawY representativeQueries raw *
            row256RawX representativeQueries raw ^ (degree : ℕ) := by
  classical
  letI : NeZero (2 : K) := ⟨two_ne_zero_of_deployed_algebra⟩
  ext raw degree
  have hbase := congrArg (fun matrix ↦ matrix (0 : Fin 1) degree)
    (naturalEval_mul_monomialToNatural_rect
      (K := K) (m := 64)
      (fun _ : Fin 1 ↦ row256RawX representativeQueries raw))
  simp only [Matrix.mul_apply, naturalEvalMatrix, monomialEvalMatrix] at hbase
  rw [Matrix.mul_apply]
  simp only [row256NaturalQMatrix]
  calc
    (∑ natural : Fin 64,
        row256RawWeight (K := K) storedQueries raw *
            row256RawY representativeQueries raw *
              (naturalLinePoly K natural).eval
                (row256RawX representativeQueries raw) *
          monomialToNatural K 64 natural degree) =
        (row256RawWeight (K := K) storedQueries raw *
            row256RawY representativeQueries raw) *
          ∑ natural : Fin 64,
            (naturalLinePoly K natural).eval
                (row256RawX representativeQueries raw) *
              monomialToNatural K 64 natural degree := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro natural _
      ring
    _ = _ := by rw [hbase]

/-- Block-major ordinary evaluation after the two natural conversions. -/
def row256OrdinaryPMatrix
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    Matrix RawCoordinate (Fin 64) K :=
  fun raw degree ↦
    row256RawWeight (K := K) storedQueries raw *
      row256RawX representativeQueries raw ^ (degree : ℕ)

def row256OrdinaryQMatrix
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    Matrix RawCoordinate (Fin 64) K :=
  fun raw degree ↦
    row256RawWeight (K := K) storedQueries raw *
      row256RawY representativeQueries raw *
        row256RawX representativeQueries raw ^ (degree : ℕ)

/-- Block-major ordinary evaluation after the two natural conversions. -/
noncomputable def row256OrdinaryBlockRawMap
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    (Fin 128 → K) →ₗ[K] RawView K :=
  ((row256OrdinaryPMatrix (K := K)
      storedQueries representativeQueries).mulVecLin.comp
        row256OrdinaryP) +
    ((row256OrdinaryQMatrix (K := K)
      storedQueries representativeQueries).mulVecLin.comp
        row256OrdinaryQ)

/-- Existing natural-basis conversion algebra closes both blocks
simultaneously. -/
theorem row256Natural_after_conversion
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    (row256NaturalPhysicalRawMap (K := K)
      storedQueries representativeQueries).comp
        (row256OrdinaryToInterleavedNatural K) =
      row256OrdinaryBlockRawMap (K := K)
        storedQueries representativeQueries := by
  apply LinearMap.ext
  intro ordinary
  funext raw
  change
    (row256NaturalPMatrix (K := K) storedQueries representativeQueries).mulVec
        (row256PhysicalPRead
          (row256OrdinaryToInterleavedNatural K ordinary)) raw +
      (row256NaturalQMatrix (K := K) storedQueries representativeQueries).mulVec
        (row256PhysicalQRead
          (row256OrdinaryToInterleavedNatural K ordinary)) raw = _
  rw [row256PhysicalPRead_after_conversion,
    row256PhysicalQRead_after_conversion,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    row256NaturalPMatrix_mul_conversion,
    row256NaturalQMatrix_mul_conversion]
  rfl

/-- Entrywise identification of the already-proved ordinary block model with
the exact query-major/runtime-slot matrix used by Component B. -/
theorem wireOrderedExtendedRow256FibreEval_entry
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount)
    (raw : RawCoordinate) (column : Fin 128) :
    wireOrderedExtendedRow256FibreEval (L := K) representativeQueries
        (row256ModelWeight storedQueries) raw column =
      if h : (column : ℕ) < 64 then
        row256OrdinaryPMatrix (K := K) storedQueries representativeQueries
          raw ⟨column, h⟩
      else
        row256OrdinaryQMatrix (K := K) storedQueries representativeQueries
          raw ⟨(column : ℕ) - 64, by omega⟩ := by
  by_cases h : (column : ℕ) < 64
  · rw [dif_pos h]
    simp [wireOrderedExtendedRow256FibreEval,
      extendedRow256FibreEval, row256FibreEval, h,
      row256OrdinaryPMatrix, row256RawWeight, row256RawX,
      rawToFibreIndex, map_mul, map_pow]
  · rw [dif_neg h]
    simp [wireOrderedExtendedRow256FibreEval,
      extendedRow256FibreEval, row256FibreEval, h,
      row256OrdinaryQMatrix, row256RawWeight, row256RawX,
      row256RawY, rawToFibreIndex, map_mul, map_pow]
    ring

omit [Algebra DeployedField K] in
private theorem row256OrdinaryP_single_of_lt
    (column : Fin 128) (h : (column : ℕ) < 64) :
    row256OrdinaryP (K := K) (Pi.single column 1) =
      Pi.single (⟨column, h⟩ : Fin 64) 1 := by
  classical
  funext index
  simp [row256OrdinaryP, Pi.single_apply, Fin.ext_iff]

omit [Algebra DeployedField K] in
private theorem row256OrdinaryQ_single_of_lt
    (column : Fin 128) (h : (column : ℕ) < 64) :
    row256OrdinaryQ (K := K) (Pi.single column 1) = 0 := by
  classical
  funext index
  simp [row256OrdinaryQ, Pi.single_apply, Fin.ext_iff]
  omega

omit [Algebra DeployedField K] in
private theorem row256OrdinaryP_single_of_not_lt
    (column : Fin 128) (h : ¬ (column : ℕ) < 64) :
    row256OrdinaryP (K := K) (Pi.single column 1) = 0 := by
  classical
  funext index
  simp [row256OrdinaryP, Pi.single_apply, Fin.ext_iff]
  omega

omit [Algebra DeployedField K] in
private theorem row256OrdinaryQ_single_of_not_lt
    (column : Fin 128) (h : ¬ (column : ℕ) < 64) :
    row256OrdinaryQ (K := K) (Pi.single column 1) =
      Pi.single (⟨(column : ℕ) - 64, by omega⟩ : Fin 64) 1 := by
  classical
  funext index
  let target : Fin 64 := ⟨(column : ℕ) - 64, by omega⟩
  change (Pi.single column (1 : K) : Fin 128 → K)
      (⟨64 + (index : ℕ), by omega⟩ : Fin 128) =
    (Pi.single target 1 : Fin 64 → K) index
  by_cases hi : index = target
  · subst index
    have heq : (⟨64 + (target : ℕ), by omega⟩ : Fin 128) = column := by
      apply Fin.ext
      simp only [target]
      omega
    simp [heq]
  · have hne : (⟨64 + (index : ℕ), by omega⟩ : Fin 128) ≠ column := by
      intro heq
      apply hi
      apply Fin.ext
      have hval := congrArg Fin.val heq
      change 64 + (index : ℕ) = (column : ℕ) at hval
      change (index : ℕ) = (target : ℕ)
      change (index : ℕ) = (column : ℕ) - 64
      omega
    simp [hi, hne]

/-- The p/q block-major ordinary map is literally the existing 72-by-128
ordinary matrix, including the non-lexicographic runtime sign-slot order. -/
theorem row256OrdinaryBlockRawMap_eq_wireOrdered
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    row256OrdinaryBlockRawMap (K := K)
        storedQueries representativeQueries =
      (wireOrderedExtendedRow256FibreEval (L := K) representativeQueries
        (row256ModelWeight storedQueries)).mulVecLin := by
  apply (Pi.basisFun K (Fin 128)).ext
  intro column
  funext raw
  rw [Pi.basisFun_apply]
  simp only [row256OrdinaryBlockRawMap, LinearMap.add_apply,
    LinearMap.comp_apply, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_single_one]
  change
    ((row256OrdinaryPMatrix (K := K) storedQueries representativeQueries).mulVec
        (row256OrdinaryP (Pi.single column 1)) +
      (row256OrdinaryQMatrix (K := K) storedQueries representativeQueries).mulVec
        (row256OrdinaryQ (Pi.single column 1))) raw =
      wireOrderedExtendedRow256FibreEval (L := K) representativeQueries
        (row256ModelWeight storedQueries) raw column
  by_cases h : (column : ℕ) < 64
  · rw [wireOrderedExtendedRow256FibreEval_entry, dif_pos h]
    rw [row256OrdinaryP_single_of_lt column h,
      row256OrdinaryQ_single_of_lt column h,
      Matrix.mulVec_single_one, Matrix.mulVec_zero]
    simp only [Pi.add_apply, Pi.zero_apply, add_zero, Matrix.col_apply]
  · rw [wireOrderedExtendedRow256FibreEval_entry, dif_neg h]
    rw [row256OrdinaryP_single_of_not_lt column h,
      row256OrdinaryQ_single_of_not_lt column h,
      Matrix.mulVec_zero, Matrix.mulVec_single_one]
    simp only [Pi.add_apply, Pi.zero_apply, zero_add, Matrix.col_apply]

/-- The complete algebraic capstone: natural encoder rows followed by the
canonical two-block conversion equal the exact 128-ordinary-by-72-opening
matrix used by the coverage proof. -/
theorem row256Natural_conversion_eq_wireOrdered
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) :
    (row256NaturalPhysicalRawMap (K := K)
      storedQueries representativeQueries).comp
        (row256OrdinaryToInterleavedNatural K) =
      (wireOrderedExtendedRow256FibreEval (L := K) representativeQueries
        (row256ModelWeight storedQueries)).mulVecLin := by
  rw [row256Natural_after_conversion,
    row256OrdinaryBlockRawMap_eq_wireOrdered]

omit [Algebra DeployedField K] in
private theorem row256PhysicalPRead_single (physical : Fin 128) :
    row256PhysicalPRead (K := K) (Pi.single physical 1) =
      if h : (physical : Nat) % 2 = 0 then
        Pi.single (⟨(physical : Nat) / 2, by omega⟩ : Fin 64) 1
      else 0 := by
  funext index
  have hphysical := physical.isLt
  by_cases h : (physical : Nat) % 2 = 0
  · rw [dif_pos h]
    have hdecomp := Nat.mod_add_div (physical : Nat) 2
    simp [row256PhysicalPRead, row256PhysicalP, Pi.single_apply, Fin.ext_iff]
    have heq : 2 * (index : Nat) = (physical : Nat) ↔
        (index : Nat) = (physical : Nat) / 2 := by omega
    simp [heq]
  · rw [dif_neg h]
    have hdecomp := Nat.mod_add_div (physical : Nat) 2
    have hmod := Nat.mod_lt (physical : Nat) (by omega : 0 < 2)
    simp [row256PhysicalPRead, row256PhysicalP, Pi.single_apply, Fin.ext_iff]
    omega

omit [Algebra DeployedField K] in
private theorem row256PhysicalQRead_single (physical : Fin 128) :
    row256PhysicalQRead (K := K) (Pi.single physical 1) =
      if h : (physical : Nat) % 2 = 0 then 0
      else Pi.single (⟨(physical : Nat) / 2, by omega⟩ : Fin 64) 1 := by
  funext index
  have hphysical := physical.isLt
  by_cases h : (physical : Nat) % 2 = 0
  · rw [dif_pos h]
    have hdecomp := Nat.mod_add_div (physical : Nat) 2
    simp [row256PhysicalQRead, row256PhysicalQ, Pi.single_apply, Fin.ext_iff]
    omega
  · rw [dif_neg h]
    have hdecomp := Nat.mod_add_div (physical : Nat) 2
    have hmod := Nat.mod_lt (physical : Nat) (by omega : 0 < 2)
    simp [row256PhysicalQRead, row256PhysicalQ, Pi.single_apply, Fin.ext_iff]
    have heq : 2 * (index : Nat) + 1 = (physical : Nat) ↔
        (index : Nat) = (physical : Nat) / 2 := by omega
    simp [heq]

/-- One natural basis row has exactly the factorization used by the extracted
v5 helper: row-256 weight, the odd-row y factor, and one natural-line value.
This is the bridge from the executable four-argument helper to the existing
matrix model. -/
theorem row256NaturalPhysicalRawMap_single
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount)
    (physical : Fin 128) :
    row256NaturalPhysicalRawMap (K := K)
        storedQueries representativeQueries (Pi.single physical 1) =
      fun raw ↦
        row256RawWeight (K := K) storedQueries raw *
          (if (physical : Nat) % 2 = 0 then 1
            else row256RawY representativeQueries raw) *
          naturalLineValue (row256RawX representativeQueries raw)
            ((physical : Nat) / 2) := by
  classical
  funext raw
  change
    ((row256NaturalPMatrix (K := K)
          storedQueries representativeQueries).mulVec
        (row256PhysicalPRead (Pi.single physical 1)) +
      (row256NaturalQMatrix (K := K)
          storedQueries representativeQueries).mulVec
        (row256PhysicalQRead (Pi.single physical 1))) raw = _
  by_cases h : (physical : Nat) % 2 = 0
  · rw [row256PhysicalPRead_single, dif_pos h,
      row256PhysicalQRead_single, dif_pos h,
      Matrix.mulVec_single_one, Matrix.mulVec_zero]
    simp only [Pi.add_apply, Matrix.col_apply, Pi.zero_apply, add_zero,
      row256NaturalPMatrix, if_pos h]
    rw [naturalLineValue_eq_eval]
    ring
  · rw [row256PhysicalPRead_single, dif_neg h,
      row256PhysicalQRead_single, dif_neg h,
      Matrix.mulVec_zero, Matrix.mulVec_single_one]
    simp only [Pi.add_apply, Pi.zero_apply, Matrix.col_apply, zero_add,
      row256NaturalQMatrix, if_neg h]
    rw [naturalLineValue_eq_eval]

end Algebra

/-! ## Exact executable boundary and deployment capstone -/

section ExecutableBoundary

variable {K : Type*} [Field K] [Algebra DeployedField K]

/-- Exact width-64 conversion identity still to be supplied by execution of
the current generic Rust conversion constructor at argument 64.  The existing
Component-A extraction proves the same function and orientation at argument
48; this interface does not pretend that the width-64 call was extracted. -/
def ExactRustRow256Conversion64
    (rustOrdinaryToNatural : (Fin 128 → K) →ₗ[K] (Fin 128 → K)) : Prop :=
  rustOrdinaryToNatural = row256OrdinaryToInterleavedNatural K

/-- The irreducible circle-encoder execution boundary: all 128 natural-basis
rows at all 72 query-major/runtime-slot openings.  This statement pins the
physical row order, stored-q18 codeword positions, and the non-lexicographic
slot order.  It is universal in the schedule, not a fixture KAT. -/
def ExactRustRow256NaturalBasisRows
    (rustRaw : Message K → RawCoordinate → K)
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) : Prop :=
  ∀ physical : Fin 128,
    rustRaw
        (structuredPadMessage K
          (row256PadVector (Pi.single physical 1))) =
      row256NaturalPhysicalRawMap (K := K)
        storedQueries representativeQueries (Pi.single physical 1)

/-- The four-argument shape of the source-extracted v5 row-256 arithmetic
helper.  The common circle encoder supplies the three scalar factors. -/
abbrev Row256NaturalHelper (K : Type*) := Fin 128 → K → K → K → K

/-- Exact arithmetic graph of the source-extracted v5-only helper. -/
def ExactRustRow256HelperArithmetic
    (rustNatural : Row256NaturalHelper K) : Prop :=
  ∀ physical factor x y,
    rustNatural physical factor x y =
      factor * (if (physical : Nat) % 2 = 0 then 1 else y) *
        naturalLineValue x ((physical : Nat) / 2)

/-- Exact identification of the common encoder rows consumed by the helper.
These are the only shared-encoder facts left after extracting the v5 helper:
row 256 is the deployed weight and rows 2/1 are signed x/y. -/
def ExactRustRow256FactorCoordinates
    (rustFactor rustX rustY : RawCoordinate → K)
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount) : Prop :=
  (∀ raw, rustFactor raw = row256RawWeight (K := K) storedQueries raw) ∧
  (∀ raw, rustX raw = row256RawX representativeQueries raw) ∧
  (∀ raw, rustY raw = row256RawY representativeQueries raw)

/-- The released raw view calls the extracted helper on every physical basis
row with the three values obtained from the pre-challenge common encoder. -/
def ExactRustRow256BasisUsesHelper
    (rustRaw : Message K → RawCoordinate → K)
    (rustNatural : Row256NaturalHelper K)
    (rustFactor rustX rustY : RawCoordinate → K) : Prop :=
  ∀ physical raw,
    rustRaw
        (structuredPadMessage K
          (row256PadVector (Pi.single physical 1))) raw =
      rustNatural physical (rustFactor raw) (rustX raw) (rustY raw)

/-- The extracted helper graph, the three common-encoder factor identities,
and the exact call site together imply the former 128-by-72 basis-row seam. -/
theorem exactRustRow256NaturalBasisRows_of_helper
    (rustRaw : Message K → RawCoordinate → K)
    (rustNatural : Row256NaturalHelper K)
    (rustFactor rustX rustY : RawCoordinate → K)
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount)
    (harithmetic : ExactRustRow256HelperArithmetic rustNatural)
    (hfactors : ExactRustRow256FactorCoordinates
      rustFactor rustX rustY storedQueries representativeQueries)
    (hcall : ExactRustRow256BasisUsesHelper
      rustRaw rustNatural rustFactor rustX rustY) :
    ExactRustRow256NaturalBasisRows
      rustRaw storedQueries representativeQueries := by
  intro physical
  funext raw
  rw [hcall physical raw, harithmetic,
    hfactors.1 raw, hfactors.2.1 raw, hfactors.2.2 raw]
  exact congrFun
    (row256NaturalPhysicalRawMap_single
      (K := K) storedQueries representativeQueries physical).symm raw

/-- The exact physical-block-to-raw linear map already present in the
coverage model. -/
noncomputable def row256PhysicalPadRawMap
    (inactive : Message K →ₗ[K] K)
    (schedule : PublicResidualSchedule K) :
    (Fin 128 → K) →ₗ[K] RawView K :=
  (rawResidualMap inactive schedule).comp
    (row256PureBlockPadLift inactive)

/-- Linearity upgrades the 128×72 basis-row execution fact to equality of the
complete physical maps. -/
theorem row256PhysicalPadRawMap_eq_natural_of_basis_rows
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount)
    (inactive : Message K →ₗ[K] K)
    (rustRaw : Message K → RawCoordinate → K)
    (schedule : PublicResidualSchedule K)
    (hscheduleRaw : rustRaw = schedule.raw)
    (hrows : ExactRustRow256NaturalBasisRows rustRaw
      storedQueries representativeQueries) :
    row256PhysicalPadRawMap inactive schedule =
      row256NaturalPhysicalRawMap (K := K)
        storedQueries representativeQueries := by
  apply (Pi.basisFun K (Fin 128)).ext
  intro physical
  rw [Pi.basisFun_apply]
  funext raw
  change schedule.raw
      (padPlusPivotEncoder inactive
        (row256PadVector (Pi.single physical 1),
          inactive
            (structuredPadMessage K
              (row256PadVector (Pi.single physical 1))))) raw = _
  rw [padPlusPivotEncoder_row256Block]
  rw [← hscheduleRaw]
  exact congrFun (hrows physical) raw

/-- The two executable identities imply the former monolithic row-256
correspondence premise.  Every conversion, interleaving, linear combination,
and runtime-slot permutation below them has disappeared into kernel proofs. -/
theorem exactRustRow256RawMatrixCorrespondence_of_basis_rows
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount)
    (inactive : Message K →ₗ[K] K)
    (rustOrdinaryToNatural : (Fin 128 → K) →ₗ[K] (Fin 128 → K))
    (rustRaw : Message K → RawCoordinate → K)
    (schedule : PublicResidualSchedule K)
    (hscheduleRaw : rustRaw = schedule.raw)
    (hconversion : ExactRustRow256Conversion64 rustOrdinaryToNatural)
    (hrows : ExactRustRow256NaturalBasisRows rustRaw
      storedQueries representativeQueries) :
    UnmetDeployment.ExactRustRow256RawMatrixCorrespondence
        storedQueries representativeQueries inactive
        rustOrdinaryToNatural rustRaw := by
  constructor
  · exact hconversion
  · intro ordinary
    dsimp only
    rw [hconversion]
    rw [padPlusPivotEncoder_row256Block]
    rw [hscheduleRaw]
    have hphysical := LinearMap.congr_fun
      (row256PhysicalPadRawMap_eq_natural_of_basis_rows
        storedQueries representativeQueries inactive rustRaw schedule
        hscheduleRaw hrows)
      (row256OrdinaryToInterleavedNatural K ordinary)
    have hpure :
        row256PhysicalPadRawMap inactive schedule
            (row256OrdinaryToInterleavedNatural K ordinary) =
          schedule.raw
            (structuredPadMessage K
              (row256PadVector
                (row256OrdinaryToInterleavedNatural K ordinary))) := by
      change schedule.raw
        (padPlusPivotEncoder inactive
          (row256PadVector
              (row256OrdinaryToInterleavedNatural K ordinary),
            inactive
              (structuredPadMessage K
                (row256PadVector
                  (row256OrdinaryToInterleavedNatural K ordinary))))) = _
      rw [padPlusPivotEncoder_row256Block]
    have halgebra := LinearMap.congr_fun
      (row256Natural_conversion_eq_wireOrdered
        (K := K) storedQueries representativeQueries) ordinary
    have hchain := hpure.symm.trans (hphysical.trans halgebra)
    funext raw
    exact congrFun hchain raw

/-- Direct closure of the coverage theorem's commuting-square premise from
the narrowed executable facts. -/
theorem row256RawMapCommutes_of_basis_rows
    (storedQueries representativeQueries :
      Fin queryCount → Fin fibreCount)
    (inactive : Message K →ₗ[K] K)
    (rustOrdinaryToNatural : (Fin 128 → K) →ₗ[K] (Fin 128 → K))
    (rustRaw : Message K → RawCoordinate → K)
    (rustMLE : Message K → MLECoordinate → K)
    (schedule : PublicResidualSchedule K)
    (hschedule : UnmetDeployment.ExactRustPublicResidualScheduleCorrespondence
      rustRaw rustMLE schedule)
    (hconversion : ExactRustRow256Conversion64 rustOrdinaryToNatural)
    (hrows : ExactRustRow256NaturalBasisRows rustRaw
      storedQueries representativeQueries) :
    Row256RawMapCommutes inactive schedule
      storedQueries representativeQueries := by
  apply UnmetDeployment.row256RawMapCommutes_of_correspondence
    storedQueries representativeQueries inactive rustOrdinaryToNatural
      rustRaw rustMLE schedule hschedule
  exact exactRustRow256RawMatrixCorrespondence_of_basis_rows
    storedQueries representativeQueries inactive rustOrdinaryToNatural
      rustRaw schedule hschedule.1 hconversion hrows

end ExecutableBoundary

/-! ## Axiom audit -/

#print axioms row256NaturalPMatrix_mul_conversion
#print axioms row256NaturalQMatrix_mul_conversion
#print axioms row256Natural_after_conversion
#print axioms wireOrderedExtendedRow256FibreEval_entry
#print axioms row256OrdinaryBlockRawMap_eq_wireOrdered
#print axioms row256Natural_conversion_eq_wireOrdered
#print axioms row256NaturalPhysicalRawMap_single
#print axioms exactRustRow256NaturalBasisRows_of_helper
#print axioms row256PhysicalPadRawMap_eq_natural_of_basis_rows
#print axioms exactRustRow256RawMatrixCorrespondence_of_basis_rows
#print axioms row256RawMapCommutes_of_basis_rows

end AspisV5ComponentBRow256Correspondence
