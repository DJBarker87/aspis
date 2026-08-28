import AspisFormal.K1.V7Tag73ExactParsedProofSourceBinding
import AspisFormal.K1.V7Tag73RawProofGammaNonBindingAudit

/-!
# Parsed one-fold schedule source non-binding audit

The production `V7CompactOneFoldWire` does not contain a total mathematical
one-fold schedule.  In particular, its bytes do not contain the two total
`Fin 262144` inverse tables carried by `Tag73K12ParsedProof.schedule`.

This module records the corresponding boundary in the main operational model.
The checked raw-return predicate inspects the public context and prover
messages but treats `rawProof` as opaque.  Hence it also accepts a replacement
whose schedule has identically-zero inverse tables, even though that schedule
cannot satisfy `ExactOneFoldInverseTables`.  This does not claim that the Rust
parser produces the replacement.  It proves that the current checked-return
interface cannot derive the inverse-table field of
`ExactParsedProofSourceBinding`; a source/model construction of the canonical
schedule is required.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ParsedScheduleSourceNonBindingAudit

open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73RawProofGammaNonBindingAudit
open AspisK1.V7Tag73RawSameTapeSource
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A total schedule whose inverse tables are deliberately invalid. -/
def zeroInverseSchedule (alpha : QM31Exact) : ExactSchedule :=
  { alpha := alpha
    circleInv2x := fun _ => 0
    circleInv2y := fun _ => 0 }

theorem zero_inverse_schedule_is_not_exact (alpha : QM31Exact) :
    ¬ ExactOneFoldInverseTables (zeroInverseSchedule alpha) := by
  intro exactTables
  have impossible := exactTables.1 (0 : Fin 262144)
  simp [zeroInverseSchedule] at impossible

/-- Replacing only the total schedule leaves the checked raw return and every
prover-owned message intact. -/
def replaceParsedSchedule (proof : Tag73K12ParsedProof)
    (schedule : ExactSchedule) : Tag73K12ParsedProof :=
  { proof with schedule := schedule }

@[simp] theorem replace_parsed_schedule_schedule
    (proof : Tag73K12ParsedProof) (schedule : ExactSchedule) :
    (replaceParsedSchedule proof schedule).schedule = schedule := by
  rfl

/-- Every checked raw result has a checked, message-identical replacement
whose total inverse-table equations are false.  Therefore those equations
cannot follow from checked raw-return success alone. -/
theorem checked_raw_return_has_message_identical_invalid_schedule
    {Statement Payload : Type*}
    (value : CheckedRawTag73AdversaryReturnedValue Statement
      Tag73K12ParsedProof Payload) :
    ∃ replacement : CheckedRawTag73AdversaryReturnedValue Statement
        Tag73K12ParsedProof Payload,
      replacement.rawMessages = value.rawMessages ∧
        ¬ ExactOneFoldInverseTables
          replacement.1.publicProof.proof.rawProof.schedule := by
  let proof := value.1.publicProof.proof.rawProof
  let schedule := zeroInverseSchedule proof.schedule.alpha
  let replacement := replaceCheckedRawProof value
    (replaceParsedSchedule proof schedule)
  refine ⟨replacement, replaceCheckedRawProof_rawMessages _ _, ?_⟩
  change ¬ ExactOneFoldInverseTables schedule
  exact zero_inverse_schedule_is_not_exact proof.schedule.alpha

#print axioms zero_inverse_schedule_is_not_exact
#print axioms replace_parsed_schedule_schedule
#print axioms checked_raw_return_has_message_identical_invalid_schedule

end

end AspisK1.V7Tag73ParsedScheduleSourceNonBindingAudit
