import AspisFormal.K1.V7Tag73ExactParsedProofSourceBinding
import AspisFormal.K1.V7Tag73RawProofGammaNonBindingAudit

/-!
# Concrete parsed-proof source-boundary audit

The raw Tag-73 return checker validates the public context and prover-owned
messages, but treats the parsed proof as opaque.  This module specializes that
fact to the exact `Tag73K12ParsedProof` consumed by K1.3--K1.5.  Replacing its
verifier-derived fields preserves the checked raw return and every prover
message.  Consequently an Aeneas/source theorem connecting the production
parser and transcript result to these fields is logically necessary; the raw
return interface alone cannot construct `ExactParsedProofSourceBinding`.

This is a positive executable audit.  It adds no premise to a probability
theorem and is not used to manufacture a source binding.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactParsedProofSourceBoundaryAudit

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73RawProofGammaNonBindingAudit
open AspisK1.V7Tag73RawSameTapeSource
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness

noncomputable section

/-- Replace all verifier-derived fields of the exact K1.2/K1.3 parsed view,
while retaining the two-tree openings that belong to the proof bytes. -/
def replaceVerifierDerivedParsedFields
    (proof : Tag73K12ParsedProof)
    (gamma : QM31Exact)
    (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule)
    (queries : QuerySchedule 16 262144) : Tag73K12ParsedProof :=
  { openings := proof.openings
    gamma := gamma
    disclosedFinal := disclosedFinal
    schedule := schedule
    queries := queries }

@[simp] theorem replace_verifier_derived_fields_openings
    (proof : Tag73K12ParsedProof)
    (gamma : QM31Exact)
    (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule)
    (queries : QuerySchedule 16 262144) :
    (replaceVerifierDerivedParsedFields proof gamma disclosedFinal schedule
      queries).openings = proof.openings := by
  rfl

@[simp] theorem replace_verifier_derived_fields_gamma
    (proof : Tag73K12ParsedProof)
    (gamma : QM31Exact)
    (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule)
    (queries : QuerySchedule 16 262144) :
    (replaceVerifierDerivedParsedFields proof gamma disclosedFinal schedule
      queries).gamma = gamma := by
  rfl

@[simp] theorem replace_verifier_derived_fields_disclosed_final
    (proof : Tag73K12ParsedProof)
    (gamma : QM31Exact)
    (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule)
    (queries : QuerySchedule 16 262144) :
    (replaceVerifierDerivedParsedFields proof gamma disclosedFinal schedule
      queries).disclosedFinal = disclosedFinal := by
  rfl

@[simp] theorem replace_verifier_derived_fields_schedule
    (proof : Tag73K12ParsedProof)
    (gamma : QM31Exact)
    (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule)
    (queries : QuerySchedule 16 262144) :
    (replaceVerifierDerivedParsedFields proof gamma disclosedFinal schedule
      queries).schedule = schedule := by
  rfl

@[simp] theorem replace_verifier_derived_fields_queries
    (proof : Tag73K12ParsedProof)
    (gamma : QM31Exact)
    (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule)
    (queries : QuerySchedule 16 262144) :
    (replaceVerifierDerivedParsedFields proof gamma disclosedFinal schedule
      queries).queries = queries := by
  rfl

@[simp] theorem checked_raw_return_accepts_replaced_verifier_fields
    {Statement Payload : Type*}
    (value : CheckedRawTag73AdversaryReturnedValue Statement
      Tag73K12ParsedProof Payload)
    (gamma : QM31Exact)
    (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule)
    (queries : QuerySchedule 16 262144) :
    (replaceCheckedRawProof value
      (replaceVerifierDerivedParsedFields
        value.1.publicProof.proof.rawProof gamma disclosedFinal schedule
          queries)).rawMessages = value.rawMessages := by
  exact replaceCheckedRawProof_rawMessages _ _

@[simp] theorem checked_raw_return_replaced_gamma_is_arbitrary
    {Statement Payload : Type*}
    (value : CheckedRawTag73AdversaryReturnedValue Statement
      Tag73K12ParsedProof Payload)
    (gamma : QM31Exact)
    (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule)
    (queries : QuerySchedule 16 262144) :
    (replaceCheckedRawProof value
      (replaceVerifierDerivedParsedFields
        value.1.publicProof.proof.rawProof gamma disclosedFinal schedule
          queries)).1.publicProof.proof.rawProof.gamma = gamma := by
  rfl

#print axioms replace_verifier_derived_fields_openings
#print axioms replace_verifier_derived_fields_gamma
#print axioms replace_verifier_derived_fields_disclosed_final
#print axioms replace_verifier_derived_fields_schedule
#print axioms replace_verifier_derived_fields_queries
#print axioms checked_raw_return_accepts_replaced_verifier_fields
#print axioms checked_raw_return_replaced_gamma_is_arbitrary

end

end AspisK1.V7Tag73ExactParsedProofSourceBoundaryAudit
