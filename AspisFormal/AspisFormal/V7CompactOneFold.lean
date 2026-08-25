import Mathlib

/-!
# V7 one-fold wire arithmetic

This leaf freezes the selected V7 wire: complete C2 fibres, 256-bit private
salts, 208-bit truncated-SHA-256 Merkle digests, a cap-203 first-success query
schedule, and the unchanged V6 26+3 one-fold relation. It proves the exact
30,504-byte maximum body and the work-ratio gate.

The Merkle parameter has 104-bit generic classical collision strength. Its
concrete truncated-SHA-256 binding assumption remains an explicit external
interface in the complete security theorem.
-/

set_option autoImplicit false

namespace AspisV7CompactOneFold

def digestBytes : Nat := 26
def digestBits : Nat := 8 * digestBytes
def classicalCollisionBits : Nat := digestBits / 2
def fixedFieldBytes : Nat := 9936
def rootBytes : Nat := 2 * digestBytes
def workNonceBytes : Nat := 24
def queryCount : Nat := 16
def c1BytesPerQuery : Nat := 403
def disclosedC2ValuesPerQuery : Nat := 12
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

theorem digest_bits_eq : digestBits = 208 := by
  norm_num [digestBits, digestBytes]

theorem classical_collision_bits_eq : classicalCollisionBits = 104 := by
  norm_num [classicalCollisionBits, digestBits, digestBytes]

theorem c2_values_are_complete : disclosedC2ValuesPerQuery = 3 * 4 := by
  norm_num [disclosedC2ValuesPerQuery]

theorem c2_bytes_per_query_eq : c2BytesPerQuery = 186 := by
  norm_num [c2BytesPerQuery, c2LimbsPerQuery, disclosedC2ValuesPerQuery]

theorem query_bytes_eq : queryBytes = 621 := by
  norm_num [queryBytes, c1BytesPerQuery, c2BytesPerQuery, c2LimbsPerQuery,
    disclosedC2ValuesPerQuery, privateSaltBytesPerQuery]

theorem query_section_bytes_eq : querySectionBytes = 9936 := by
  norm_num [querySectionBytes, queryCount, queryBytes, c1BytesPerQuery,
    c2BytesPerQuery, c2LimbsPerQuery, disclosedC2ValuesPerQuery,
    privateSaltBytesPerQuery]

theorem max_body_bytes_eq : maxBodyBytes = 30504 := by
  norm_num [maxBodyBytes, fixedFieldBytes, rootBytes, workNonceBytes,
    querySectionBytes, queryCount, queryBytes, c1BytesPerQuery,
    c2BytesPerQuery, c2LimbsPerQuery, disclosedC2ValuesPerQuery,
    privateSaltBytesPerQuery, frontierCapPerTree, digestBytes]

theorem body_headroom_eq : productionLimitBytes - maxBodyBytes = 216 := by
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
of V6's three-stage expected work and remains below the hard 3/2 gate. -/
theorem honest_work_ratio_below_three_halves :
    2 * v7HonestWork ≤ 3 * v6HonestWork := by
  norm_num [v7HonestWork, v6HonestWork]

#print axioms digest_bits_eq
#print axioms classical_collision_bits_eq
#print axioms c2_values_are_complete
#print axioms max_body_bytes_eq
#print axioms max_body_lt_thirty_kib
#print axioms honest_work_ratio_below_three_halves

end AspisV7CompactOneFold
