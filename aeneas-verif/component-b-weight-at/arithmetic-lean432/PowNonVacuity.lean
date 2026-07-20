import M31PowProof
import CM31PowProof
import QM31PowProof

/-! Concrete canonical witnesses for every generated pow capstone domain. -/

open Aeneas Aeneas.Std

namespace AspisAeneasPowNonVacuity

open AspisCorePow

theorem canonical_m31_pow_domain_nonempty :
    ∃ x : field.M31, AspisAeneasM31Pow.CanonicalRawM31 x.val := by
  refine ⟨0#u32, ?_⟩
  norm_num [AspisAeneasM31ReduceU64.CanonicalRawM31,
    AspisAeneasM31ReduceU64.m31Modulus]

theorem canonical_cm31_pow_domain_nonempty :
    ∃ x : field.CM31, AspisAeneasCM31Pow.CanonicalCM31 x := by
  refine ⟨⟨0#u32, 0#u32⟩, ?_⟩
  norm_num [AspisAeneasCM31Pow.CanonicalCM31,
    AspisAeneasCM31Pow.CanonicalRawM31,
    AspisAeneasCM31Pow.m31Modulus]

theorem canonical_qm31_pow_domain_nonempty :
    ∃ x : field.QM31, AspisAeneasQM31Pow.CanonicalQM31 x := by
  exact AspisAeneasQM31Pow.canonical_qm31_pow_nonempty

#print axioms canonical_m31_pow_domain_nonempty
#print axioms canonical_cm31_pow_domain_nonempty
#print axioms canonical_qm31_pow_domain_nonempty

end AspisAeneasPowNonVacuity
