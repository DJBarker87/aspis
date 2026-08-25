import AspisFormal.V5ComponentCQM31TowerExact
import Mathlib

/-!
# V7 compact one-fold wire and omitted-value reconstruction

This leaf freezes the selected wire-only successor to Tag 72.  It proves the
exact 30,672-byte maximum body, the 48-byte margin below 30 KiB, the honest
work-ratio gate, and the field identity used to reconstruct one omitted `D`
value in each queried arity-four fibre.

The Merkle digest is shortened to 216 bits, but the 256-bit private salts are
not shortened.  This file records the generic 108-bit classical collision
strength; connecting a concrete truncated-SHA-256 binding assumption to the
complete security experiment is a separate release obligation.
-/

set_option autoImplicit false

namespace AspisV7CompactOneFold

def digestBytes : Nat := 27
def digestBits : Nat := 8 * digestBytes
def classicalCollisionBits : Nat := digestBits / 2
def fixedFieldBytes : Nat := 9936
def rootBytes : Nat := 2 * digestBytes
def workNonceBytes : Nat := 24
def queryCount : Nat := 16
def c1BytesPerQuery : Nat := 403
def disclosedC2ValuesPerQuery : Nat := 11
def c2LimbsPerQuery : Nat := 4 * disclosedC2ValuesPerQuery
def c2BytesPerQuery : Nat := (31 * c2LimbsPerQuery + 7) / 8
def privateSaltBytesPerQuery : Nat := 32
def queryBytes : Nat := c1BytesPerQuery + c2BytesPerQuery + privateSaltBytesPerQuery
def querySectionBytes : Nat := queryCount * queryBytes
def frontierCapPerTree : Nat := 203
def maxBodyBytes : Nat :=
  fixedFieldBytes + rootBytes + workNonceBytes + querySectionBytes +
    2 * frontierCapPerTree * digestBytes
def productionLimitBytes : Nat := 30 * 1024

def v6HonestWork : Nat := 2 ^ 34 + 2 ^ 31 + 2 ^ 34
def v7HonestWork : Nat := 2 ^ 35 + 2 ^ 31 + 2 ^ 34

theorem digest_bits_eq : digestBits = 216 := by
  norm_num [digestBits, digestBytes]

theorem classical_collision_bits_eq : classicalCollisionBits = 108 := by
  norm_num [classicalCollisionBits, digestBits, digestBytes]

theorem c2_bytes_per_query_eq : c2BytesPerQuery = 171 := by
  norm_num [c2BytesPerQuery, c2LimbsPerQuery, disclosedC2ValuesPerQuery]

theorem query_bytes_eq : queryBytes = 606 := by
  norm_num [queryBytes, c1BytesPerQuery, c2BytesPerQuery, c2LimbsPerQuery,
    disclosedC2ValuesPerQuery, privateSaltBytesPerQuery]

theorem query_section_bytes_eq : querySectionBytes = 9696 := by
  norm_num [querySectionBytes, queryCount, queryBytes, c1BytesPerQuery,
    c2BytesPerQuery, c2LimbsPerQuery, disclosedC2ValuesPerQuery,
    privateSaltBytesPerQuery]

theorem max_body_bytes_eq : maxBodyBytes = 30672 := by
  norm_num [maxBodyBytes, fixedFieldBytes, rootBytes, workNonceBytes,
    querySectionBytes, queryCount, queryBytes, c1BytesPerQuery,
    c2BytesPerQuery, c2LimbsPerQuery, disclosedC2ValuesPerQuery,
    privateSaltBytesPerQuery, frontierCapPerTree, digestBytes]

theorem body_headroom_eq : productionLimitBytes - maxBodyBytes = 48 := by
  norm_num [productionLimitBytes, maxBodyBytes, fixedFieldBytes, rootBytes,
    workNonceBytes, querySectionBytes, queryCount, queryBytes,
    c1BytesPerQuery, c2BytesPerQuery, c2LimbsPerQuery,
    disclosedC2ValuesPerQuery, privateSaltBytesPerQuery,
    frontierCapPerTree, digestBytes]

theorem max_body_lt_thirty_kib : maxBodyBytes < productionLimitBytes := by
  norm_num [productionLimitBytes, maxBodyBytes, fixedFieldBytes, rootBytes,
    workNonceBytes, querySectionBytes, queryCount, queryBytes,
    c1BytesPerQuery, c2BytesPerQuery, c2LimbsPerQuery,
    disclosedC2ValuesPerQuery, privateSaltBytesPerQuery,
    frontierCapPerTree, digestBytes]

/-- Raising only the first work gate from 34 to 35 bits costs exactly 25/17
of V6's three-stage expected work, hence remains below the hard 3/2 gate. -/
theorem honest_work_ratio_below_three_halves :
    2 * v7HonestWork ≤ 3 * v6HonestWork := by
  norm_num [v7HonestWork, v6HonestWork]

section Reconstruction

variable {K : Type*} [Field K]

def linearFold (coefficients values : Fin 4 → K) : K :=
  ∑ slot, coefficients slot * values slot

theorem some_fold_coefficient_nonzero
    (coefficients : Fin 4 → K)
    (hsum : ∑ slot, coefficients slot = 1) :
    ∃ slot, coefficients slot ≠ 0 := by
  by_contra hall
  push Not at hall
  have : (∑ slot, coefficients slot) = 0 := by simp [hall]
  rw [this] at hsum
  exact zero_ne_one hsum

theorem linearFold_update_add
    (coefficients values : Fin 4 → K) (slot : Fin 4) (delta : K) :
    linearFold coefficients (Function.update values slot (values slot + delta)) =
      linearFold coefficients values + coefficients slot * delta := by
  classical
  fin_cases slot <;>
    simp [linearFold, Fin.sum_univ_four] <;>
    ring

def reconstructedValue
    (coefficients values : Fin 4 → K) (slot : Fin 4)
    (target dPower : K) : K :=
  (target - linearFold coefficients values) / (coefficients slot * dPower)

/-- The omitted D value is uniquely recovered from the same fold equation
that V6 previously checked after sending all four values. -/
theorem reconstruct_omitted_value_restores_fold
    (coefficients values : Fin 4 → K) (slot : Fin 4)
    (target dPower : K)
    (hCoefficient : coefficients slot ≠ 0)
    (hDPower : dPower ≠ 0) :
    linearFold coefficients
        (Function.update values slot
          (values slot + dPower *
            reconstructedValue coefficients values slot target dPower)) =
      target := by
  rw [linearFold_update_add]
  simp only [reconstructedValue]
  field_simp
  ring

/-- Specialization to the literal deployed QM31 tower used by the Rust host
reference. -/
theorem deployed_qm31_reconstruction
    (coefficients values : Fin 4 → AspisV5ComponentCQM31TowerExact.QM31Exact)
    (slot : Fin 4) (target dPower : AspisV5ComponentCQM31TowerExact.QM31Exact)
    (hCoefficient : coefficients slot ≠ 0)
    (hDPower : dPower ≠ 0) :
    linearFold coefficients
        (Function.update values slot
          (values slot + dPower *
            reconstructedValue coefficients values slot target dPower)) =
      target :=
  reconstruct_omitted_value_restores_fold coefficients values slot target dPower
    hCoefficient hDPower

end Reconstruction

#print axioms max_body_bytes_eq
#print axioms honest_work_ratio_below_three_halves
#print axioms some_fold_coefficient_nonzero
#print axioms reconstruct_omitted_value_restores_fold
#print axioms deployed_qm31_reconstruction

end AspisV7CompactOneFold
