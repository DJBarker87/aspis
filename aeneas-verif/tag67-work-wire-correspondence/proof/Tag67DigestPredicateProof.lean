import Tag67DigestPredicate

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisTag67DigestPredicate

/-- Maintained mathematical view of the first eight digest bytes. -/
def digestHeadBE (digest : Array Std.U8 32#usize) : Std.U64 :=
  core.num.U64.from_be_bytes (Array.make 8#usize [
    digest.val[0]!, digest.val[1]!, digest.val[2]!, digest.val[3]!,
    digest.val[4]!, digest.val[5]!, digest.val[6]!, digest.val[7]!])

/-- Maintained work predicate: zero work is unconditional; otherwise the
big-endian digest head must lie strictly below the exact power-of-two bound. -/
def digestHasLeadingZeroBits
    (digest : Array Std.U8 32#usize) (bits : Std.U8) : Prop :=
  bits.val = 0 ∨
    (digestHeadBE digest).val <
      (Std.U64.wrapping_shl 1#u64
        (Std.U32.wrapping_sub 64#u32 (UScalar.cast .U32 bits))).val

/-- The pinned-Aeneas extraction of the pure Rust helper equals the maintained
predicate for every digest and every valid (at most 64-bit) difficulty. -/
theorem extracted_digest_predicate_iff_maintained
    (digest : Array Std.U8 32#usize) (bits : Std.U8) :
    aspis_core.transcript.digest_has_leading_zero_bits digest bits = ok true ↔
      digestHasLeadingZeroBits digest bits := by
  by_cases hzero : bits.val = 0
  · have hbits : bits = 0#u8 := by
      apply UScalar.eq_of_val_eq
      simpa using hzero
    simp [aspis_core.transcript.digest_has_leading_zero_bits,
      digestHasLeadingZeroBits, hbits]
  · have hbits : bits ≠ 0#u8 := by
      intro h
      apply hzero
      simp [h]
    simp [aspis_core.transcript.digest_has_leading_zero_bits,
      digestHasLeadingZeroBits, digestHeadBE, Array.index_usize, lift,
      hbits, hzero]

/-- Threshold-minus-one is accepted and the threshold itself is rejected for
all six deployed Tag-67 difficulties. -/
theorem deployed_difficulty_boundary_teeth :
    (∀ below atDigest,
      (digestHeadBE below).val = 134217727 → (digestHeadBE atDigest).val = 134217728 →
      digestHasLeadingZeroBits below 37#u8 ∧ ¬ digestHasLeadingZeroBits atDigest 37#u8) ∧
    (∀ below atDigest,
      (digestHeadBE below).val = 1073741823 → (digestHeadBE atDigest).val = 1073741824 →
      digestHasLeadingZeroBits below 34#u8 ∧ ¬ digestHasLeadingZeroBits atDigest 34#u8) ∧
    (∀ below atDigest,
      (digestHeadBE below).val = 2147483647 → (digestHeadBE atDigest).val = 2147483648 →
      digestHasLeadingZeroBits below 33#u8 ∧ ¬ digestHasLeadingZeroBits atDigest 33#u8) ∧
    (∀ below atDigest,
      (digestHeadBE below).val = 17179869183 → (digestHeadBE atDigest).val = 17179869184 →
      digestHasLeadingZeroBits below 30#u8 ∧ ¬ digestHasLeadingZeroBits atDigest 30#u8) ∧
    (∀ below atDigest,
      (digestHeadBE below).val = 549755813887 → (digestHeadBE atDigest).val = 549755813888 →
      digestHasLeadingZeroBits below 25#u8 ∧ ¬ digestHasLeadingZeroBits atDigest 25#u8) ∧
    (∀ below atDigest,
      (digestHeadBE below).val = 4294967295 → (digestHeadBE atDigest).val = 4294967296 →
      digestHasLeadingZeroBits below 32#u8 ∧ ¬ digestHasLeadingZeroBits atDigest 32#u8) := by
  repeat' apply And.intro
  all_goals
    intro below atDigest hbelow hat
    simp [digestHasLeadingZeroBits, hbelow, hat, Std.U64.wrapping_shl,
      Std.U32.wrapping_sub, UScalar.wrapping_shl, UScalar.wrapping_sub,
      UScalar.cast]
    decide

theorem zero_work_accepts_maximal_digest :
    ∀ digest : Array Std.U8 32#usize, digestHasLeadingZeroBits digest 0#u8 := by
  intro digest
  simp [digestHasLeadingZeroBits]

/-- Reversing the first eight bytes changes the accepted 32-bit boundary-minus
one head into a rejected big-endian head. -/
theorem digest_byte_reversal_tooth :
    ∀ canonical reversed,
      (digestHeadBE canonical).val = 4294967295 →
      (digestHeadBE reversed).val = 18446744069414584320 →
      digestHasLeadingZeroBits canonical 32#u8 ∧
        ¬ digestHasLeadingZeroBits reversed 32#u8 := by
  intro canonical reversed hcanonical hreversed
  simp [digestHasLeadingZeroBits, hcanonical, hreversed,
    Std.U64.wrapping_shl, Std.U32.wrapping_sub,
    UScalar.wrapping_shl, UScalar.wrapping_sub, UScalar.cast]
  decide

#print axioms extracted_digest_predicate_iff_maintained
#print axioms deployed_difficulty_boundary_teeth
#print axioms zero_work_accepts_maximal_digest
#print axioms digest_byte_reversal_tooth

end AspisTag67DigestPredicate
