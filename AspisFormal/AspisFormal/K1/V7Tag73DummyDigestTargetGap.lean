import AspisFormal.K1.V7Tag73ExactCompilerTargetClean

/-!
# The dummy-digest target omitted by an unseeded Tag-73 causal state

The deployed future-free verifier starts from the public all-zero 256-bit
digest.  That value is not an oracle answer, so a causal collision set that
starts with no previously seen values does not retain it.  This leaf gives a
kernel-checked local counterexample: at a later fork whose checkpoint digest
is nonzero, the zero digest belongs to neither the empty seen set, the empty
history targets, nor either current input-prefix target.

Consequently an unseeded causal state cannot prove absence of all ancestor
programming conflicts.  The minimal repair is to seed the public dummy digest
before the first exposure (equivalently, include it in every target set).  This
adds one target per exposure, changing the exact coefficient from
`choose(F,2) + F*G` to `F + choose(F,2) + F*G`.

This module proves only the local no-go and repaired arithmetic.  It does not
assert a compiler-failure cover or change the executable scheduler.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73DummyDigestTargetGap

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicPairProbabilityAudit
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73GlobalForwardReferenceBound

noncomputable section

def unrelatedOutputInput : ShaInput :=
  bytes lastByteOneDigest ++ [domSqueeze]

def unrelatedAdvanceInput : ShaInput :=
  bytes lastByteOneDigest ++ [domAdvance]

theorem last_byte_one_is_output_input_prefix :
    HasLiteralStatePrefix lastByteOneDigest unrelatedOutputInput := by
  unfold HasLiteralStatePrefix unrelatedOutputInput
  simpa using
    (List.take_append_length
      (l₁ := bytes lastByteOneDigest) (l₂ := [domSqueeze])).symm

theorem last_byte_one_is_advance_input_prefix :
    HasLiteralStatePrefix lastByteOneDigest unrelatedAdvanceInput := by
  unfold HasLiteralStatePrefix unrelatedAdvanceInput
  simpa using
    (List.take_append_length
      (l₁ := bytes lastByteOneDigest) (l₂ := [domAdvance])).symm

theorem dummy_zero_is_not_output_input_prefix :
    ¬ HasLiteralStatePrefix (zeroBytes 32) unrelatedOutputInput := by
  intro zeroPrefix
  have equal := literal_state_prefix_target_subsingleton unrelatedOutputInput
    (show zeroBytes 32 ∈ literalStatePrefixTarget unrelatedOutputInput from
      zeroPrefix)
    (show lastByteOneDigest ∈ literalStatePrefixTarget unrelatedOutputInput
      from last_byte_one_is_output_input_prefix)
  exact zero_digest_ne_last_byte_one equal

theorem dummy_zero_is_not_advance_input_prefix :
    ¬ HasLiteralStatePrefix (zeroBytes 32) unrelatedAdvanceInput := by
  intro zeroPrefix
  have equal := literal_state_prefix_target_subsingleton unrelatedAdvanceInput
    (show zeroBytes 32 ∈ literalStatePrefixTarget unrelatedAdvanceInput from
      zeroPrefix)
    (show lastByteOneDigest ∈ literalStatePrefixTarget unrelatedAdvanceInput
      from last_byte_one_is_advance_input_prefix)
  exact zero_digest_ne_last_byte_one equal

/-- The unseeded local fork target misses the public dummy digest.  This is a
concrete set-membership obstruction, not a probability or protocol premise. -/
theorem unseeded_fork_targets_miss_dummy_zero :
    zeroBytes 32 ∉
      operationalForkTargets ∅ [] unrelatedOutputInput unrelatedAdvanceInput := by
  simp only [operationalForkTargets, operationalHistoryTargets,
    historyLiteralTargets, Finset.empty_union, Finset.mem_union,
    mem_one_input_literal_targets_iff]
  exact not_or_intro dummy_zero_is_not_output_input_prefix
    dummy_zero_is_not_advance_input_prefix

/-- The repaired cap list is the existing causal cap family with one public
dummy target added at every exposure. -/
def dummySeededTargetCaps (F G : Nat) : List Nat :=
  tag73GlobalForwardReferenceCaps F (G + 1)

def dummySeededTargetCoefficient (F G : Nat) : Nat :=
  F + F.choose 2 + F * G

theorem dummy_seeded_target_caps_length (F G : Nat) :
    (dummySeededTargetCaps F G).length = F := by
  exact tag73_global_forward_reference_caps_length F (G + 1)

theorem dummy_seeded_target_caps_sum_exact (F G : Nat) :
    (dummySeededTargetCaps F G).sum = dummySeededTargetCoefficient F G := by
  rw [dummySeededTargetCaps,
    tag73_global_forward_reference_caps_sum_exact]
  unfold tag73GlobalForwardReferenceCoefficient dummySeededTargetCoefficient
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem dummy_seeded_target_coefficient_expansion (F G : Nat) :
    tag73GlobalForwardReferenceCoefficient F (G + 1) =
      F + F.choose 2 + F * G := by
  unfold tag73GlobalForwardReferenceCoefficient
  rw [Nat.mul_add, Nat.mul_one]
  omega

#print axioms last_byte_one_is_output_input_prefix
#print axioms last_byte_one_is_advance_input_prefix
#print axioms dummy_zero_is_not_output_input_prefix
#print axioms dummy_zero_is_not_advance_input_prefix
#print axioms unseeded_fork_targets_miss_dummy_zero
#print axioms dummy_seeded_target_caps_length
#print axioms dummy_seeded_target_caps_sum_exact
#print axioms dummy_seeded_target_coefficient_expansion

end

end AspisK1.V7Tag73DummyDigestTargetGap
