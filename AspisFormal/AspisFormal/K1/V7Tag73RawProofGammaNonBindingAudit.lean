import AspisFormal.K1.V7Tag73RawSameTapeSource

/-!
# Raw-proof gamma non-binding audit

The raw Tag-73 return checker binds the prover-controlled message context to
the public instance.  It deliberately does not parse or validate the opaque
`rawProof` field.  This file records that boundary positively: replacing only
the opaque proof preserves both the checked-return witness and every raw
prover message.

Because the construction is polymorphic in the opaque proof type, every
field of a concrete parsed proof -- including its gamma coordinate -- lies
outside this checked-return boundary.  This is not a claim that a deployed
parser accepts a replacement.  It proves that the current checked-return
interface alone cannot supply any parser/operational-gamma equality.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RawProofGammaNonBindingAudit

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73RawSameTapeSource

noncomputable section

/-- Replace only the opaque proof component of a context-checked raw return.
The executable context predicate is unchanged because it reads only the raw
messages and public instance. -/
def replaceCheckedRawProof
    {Statement Proof Payload : Type*}
    (value : CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)
    (proof : Proof) :
    CheckedRawTag73AdversaryReturnedValue Statement Proof Payload :=
  ⟨{ publicProof :=
      { publicInstance := value.1.publicProof.publicInstance
        proof :=
          { rawProof := proof
            auxiliary := value.1.publicProof.proof.auxiliary
            messages := value.1.publicProof.proof.messages } } },
    value.2⟩

@[simp] theorem replaceCheckedRawProof_rawMessages
    {Statement Proof Payload : Type*}
    (value : CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)
    (proof : Proof) :
    (replaceCheckedRawProof value proof).rawMessages = value.rawMessages := by
  rfl

@[simp] theorem replaceCheckedRawProof_rawProof
    {Statement Proof Payload : Type*}
    (value : CheckedRawTag73AdversaryReturnedValue Statement Proof Payload)
    (proof : Proof) :
    (replaceCheckedRawProof value proof).1.publicProof.proof.rawProof = proof := by
  rfl

#print axioms replaceCheckedRawProof_rawMessages
#print axioms replaceCheckedRawProof_rawProof

end

end AspisK1.V7Tag73RawProofGammaNonBindingAudit
