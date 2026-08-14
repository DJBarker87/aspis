import AspisFormal.V5Tag67FalseAcceptanceDecomposition

/-!
# From the modeled Tag-67 relation verifier to relation acceptance

This file closes the pure verifier-semantics part of the first unfinished
implication in `V5Tag67FalseAcceptanceDecomposition`.

The modeled verifier below follows the success path of
`verify_v5_relation_stress_with_additive`:

1. check each of the four sumcheck boundaries in order;
2. carry the polynomial evaluation to the next round;
3. dual-fold the shared weights; and
4. check the final dot product against the carried claim.

The model starts after field decoding, OOD-point validation, weight-shape
checks, and construction of the combined main/additive weight vector.  Those
operations can only make the Rust function reject, but connecting their
successful concrete execution and the raw callback to this model still needs
one code-to-model statement.  It is named
`RustSuccessImpliesModeledRelationSuccess` below.

No current Charon/Aeneas theorem in the repository extracts
`verify_v5_relation_stress_with_additive` itself.  The source snapshot used by
the existing Tag-67 Aeneas work contains the call, while its proved selector
and work-check layer treats the callee's result as an input.  Consequently the
code-to-model statement is retained rather than claimed here.

Everything after that single boundary is proved: modeled success is exactly
the five equalities in the maintained verifier model, those equalities do not
depend on which FRI candidate is selected, and therefore every member of a
coherent candidate family satisfies `AcceptedCandidateExecution.RelationAccepts`.
-/

namespace AspisV5Tag67ModeledRelationAcceptanceBridge

open AspisV5RelationSumcheckSoundness
open AspisV5FriRelationCandidateBridge
open AspisV5Tag67RelationListInclusion
open AspisV5Tag67FalseAcceptanceDecomposition

variable {K : Type*} [Field K]

/-! ## Candidate-independent verifier state -/

/-- Claim carried out of relation round zero. -/
noncomputable def sharedClaim1
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (history : RelationRoundChallenges K) : K :=
  family.round0.nextClaim () history

/-- Claim carried out of relation round one. -/
noncomputable def sharedClaim2
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (history : RelationRoundChallenges K × RelationRoundChallenges K) : K :=
  family.round1.nextClaim history.1 history.2

/-- Claim carried out of relation round two. -/
noncomputable def sharedClaim3
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (history : (RelationRoundChallenges K × RelationRoundChallenges K) ×
      RelationRoundChallenges K) : K :=
  family.round2.nextClaim history.1 history.2

/-- Claim carried out of the fourth relation round. -/
noncomputable def sharedFinalClaim
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K) : K :=
  family.round3.nextClaim challenges.1 challenges.2

/-- Shared weights after relation round zero. -/
def sharedWeights1
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (history : RelationRoundChallenges K) : Fin 256 → K :=
  family.round0.nextWeights family.initialWeights () history

/-- Shared weights after relation round one. -/
def sharedWeights2
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (history : RelationRoundChallenges K × RelationRoundChallenges K) :
    Fin 64 → K :=
  family.round1.nextWeights (sharedWeights1 family history.1)
    history.1 history.2

/-- Shared weights after relation round two. -/
def sharedWeights3
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (history : (RelationRoundChallenges K × RelationRoundChallenges K) ×
      RelationRoundChallenges K) : Fin 16 → K :=
  family.round2.nextWeights (sharedWeights2 family history.1)
    history.1 history.2

/-- Shared four-entry weight vector after the last relation fold. -/
def sharedFinalWeights
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K) : Fin 4 → K :=
  family.round3.nextWeights (sharedWeights3 family challenges.1)
    challenges.1 challenges.2

/-! ## The five checks performed on a successful verifier path -/

/-- Round-zero boundary equality. -/
def boundaryCheck0
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K) : Prop :=
  family.round0.Accepts family.initialClaim () (round0Block challenges)

/-- Round-one boundary equality. -/
def boundaryCheck1
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K) : Prop :=
  family.round1.Accepts (sharedClaim1 family (round0Block challenges))
    (round0Block challenges) (round1Block challenges)

/-- Round-two boundary equality. -/
def boundaryCheck2
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K) : Prop :=
  family.round2.Accepts (sharedClaim2 family challenges.1.1)
    challenges.1.1 (round2Block challenges)

/-- Round-three boundary equality. -/
def boundaryCheck3
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K) : Prop :=
  family.round3.Accepts (sharedClaim3 family challenges.1)
    challenges.1 (round3Block challenges)

/-- Final dot-product equality, including the already-combined additive
covector represented by the family's shared initial weights. -/
def terminalCheck
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K) : Prop :=
  candidateClaim (sharedFinalWeights family challenges)
    (family.publishedFinal challenges) = sharedFinalClaim family challenges

/-- Candidate-independent statement of all checks on the Rust success path. -/
def SharedRelationChecks
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K) : Prop :=
  boundaryCheck0 family challenges ∧
  boundaryCheck1 family challenges ∧
  boundaryCheck2 family challenges ∧
  boundaryCheck3 family challenges ∧
  terminalCheck family challenges

/-- Data returned by the pure relation verifier model. -/
structure ModeledRelationOutput (K : Type*) where
  finalCoefficients : Fin 4 → K
  terminalClaim : K

/-- Pure success/failure control flow of the relation verifier.

The nested checks deliberately mirror Rust's early returns rather than
defining success as `SharedRelationChecks` in one step. -/
noncomputable def runModeledRelationVerifier
    {Candidate : Type*} [DecidableEq K]
    (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K) :
    Option (ModeledRelationOutput K) := by
  classical
  exact
    if boundaryCheck0 family challenges then
      if boundaryCheck1 family challenges then
        if boundaryCheck2 family challenges then
          if boundaryCheck3 family challenges then
            if terminalCheck family challenges then
              some
                { finalCoefficients := family.publishedFinal challenges
                  terminalClaim := sharedFinalClaim family challenges }
            else none
          else none
        else none
      else none
    else none

/-! ## Exact pure-model correspondence -/

section DecidableField

variable [DecidableEq K]

/-- Modeled success is equivalent to the five maintained verifier checks.
This is a biconditional, not merely a soundness direction. -/
theorem modeled_relation_success_iff_shared_checks
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K) :
  (∃ output,
      runModeledRelationVerifier family challenges = some output) ↔
      SharedRelationChecks family challenges := by
  unfold runModeledRelationVerifier SharedRelationChecks
  by_cases h0 : boundaryCheck0 family challenges <;> simp [h0]

omit [DecidableEq K] in
/-- The shared five checks are definitionally the candidate execution's
`RelationAccepts` predicate.  Candidate coefficient values do not occur in
these checks. -/
theorem shared_checks_iff_candidate_relation_accepts
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (candidate : Candidate)
    (challenges : TwelveRelationChallenges K) :
    SharedRelationChecks family challenges ↔
      (family.execution candidate).RelationAccepts challenges := by
  simp only [SharedRelationChecks, boundaryCheck0, boundaryCheck1,
    boundaryCheck2, boundaryCheck3, terminalCheck,
    CoherentCandidateFamily.execution,
    AcceptedCandidateExecution.RelationAccepts,
    AcceptedCandidateExecution.claim1, AcceptedCandidateExecution.claim2,
    AcceptedCandidateExecution.claim3, AcceptedCandidateExecution.finalClaim,
    AcceptedCandidateExecution.weights1, AcceptedCandidateExecution.weights2,
    AcceptedCandidateExecution.weights3, AcceptedCandidateExecution.finalWeights,
    sharedClaim1, sharedClaim2, sharedClaim3, sharedFinalClaim,
    sharedWeights1, sharedWeights2, sharedWeights3, sharedFinalWeights]

/-- Pure modeled verifier success gives relation acceptance for every member
of the coherent family, including whichever candidate FRI later matches. -/
theorem modeled_success_implies_all_candidate_relation_checks_accept
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (challenges : TwelveRelationChallenges K)
    (hsuccess : ∃ output,
      runModeledRelationVerifier family challenges = some output) :
    AllCandidateRelationChecksAccept family challenges := by
  have hshared :=
    (modeled_relation_success_iff_shared_checks family challenges).mp hsuccess
  intro candidate
  exact (shared_checks_iff_candidate_relation_accepts
    family candidate challenges).mp hshared

/-! ## The one remaining Rust/Aeneas boundary -/

/-- The irreducible current code-to-model premise.

For the raw acceptance predicate supplied by the complete Tag-67 callback,
every successful execution must yield success of the pure verifier above on
the decoded coherent family and challenges.  This is strictly a
source-to-model statement: its conclusion is modeled `Option` success, not
`RelationAccepts` and not membership in a soundness event.

Discharging it requires extraction or a direct proof of
`verify_v5_relation_stress_with_additive`, including its decoded values, the
main/additive weight combination, and the call site in
`verify_mode9_relation_phase`. -/
def RustSuccessImpliesModeledRelationSuccess
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (rawAccepts : TwelveRelationChallenges K → Prop) : Prop :=
  ∀ challenges, rawAccepts challenges →
    ∃ output, runModeledRelationVerifier family challenges = some output

/-- Once the single code-to-model premise is supplied, raw Tag-67 relation
acceptance implies all candidate-independent maintained relation checks. -/
theorem raw_success_implies_all_candidate_relation_checks_accept
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (rawAccepts : TwelveRelationChallenges K → Prop)
    (codeModel : RustSuccessImpliesModeledRelationSuccess family rawAccepts)
    {challenges : TwelveRelationChallenges K}
    (hraw : rawAccepts challenges) :
    AllCandidateRelationChecksAccept family challenges := by
  exact modeled_success_implies_all_candidate_relation_checks_accept
    family challenges (codeModel challenges hraw)

/-- Directly discharge the named raw-relation implication used by the honest
false-acceptance decomposition, relative only to the one code-to-model
premise. -/
theorem raw_relation_acceptance_implication_of_code_model
    {Candidate : Type*} (family : CoherentCandidateFamily K Candidate)
    (rawAccepts : TwelveRelationChallenges K → Prop)
    (codeModel : RustSuccessImpliesModeledRelationSuccess family rawAccepts) :
    RawRelationAcceptanceImplication family rawAccepts := by
  intro challenges hraw
  exact raw_success_implies_all_candidate_relation_checks_accept
    family rawAccepts codeModel hraw

#print axioms modeled_relation_success_iff_shared_checks
#print axioms shared_checks_iff_candidate_relation_accepts
#print axioms modeled_success_implies_all_candidate_relation_checks_accept
#print axioms raw_success_implies_all_candidate_relation_checks_accept
#print axioms raw_relation_acceptance_implication_of_code_model

end DecidableField

end AspisV5Tag67ModeledRelationAcceptanceBridge
