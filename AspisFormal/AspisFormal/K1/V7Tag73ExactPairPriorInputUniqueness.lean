import AspisFormal.K1.V7Tag73ExactPairCoordinateProfileInvariant

/-!
# Cross-fibre answer uniqueness inside one shared exact-root prefix

The adversary-anchor K1.3 comparison already proves that the two executions
have an identical literal root-record prefix before the selected final-work
exposure.  Cached alpha and gamma queries must be compared through that
prefix, rather than incorrectly relabelling them as later named coordinates.

This leaf records the elementary but central direction of the prefix
invariant: two machine records with the same SHA input in the shared prefix
have the same answer.  The argument uses executable fresh-input uniqueness;
it is not SHA-256 injectivity and it does not classify the logical role of the
input.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactPairPriorInputUniqueness

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Inside equal exact-root prefixes, one literal SHA input has one answer.
Actor labels are deliberately allowed to differ: an adversary-first query in
one execution may be a verifier cache hit in another, while the immutable
oracle entry is still identical. -/
theorem exact_equal_root_priors_same_input_answer_eq
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (leftPrior rightPrior : List UnifiedExposureRecord)
    (leftActor rightActor : QueryActor)
    (queryInput : ShaInput) (leftAnswer rightAnswer : Digest256)
    (priorExact : leftPrior = rightPrior)
    (leftMember :
      (.machineFresh leftActor queryInput leftAnswer : UnifiedExposureRecord) ∈
        leftPrior)
    (rightMember :
      (.machineFresh rightActor queryInput rightAnswer : UnifiedExposureRecord) ∈
        rightPrior)
    (leftPrefixMember : ∀ record, record ∈ leftPrior →
      record ∈ exactFixedRootRecords input.package.root) :
    leftAnswer = rightAnswer := by
  have rightMember' :
      (.machineFresh rightActor queryInput rightAnswer : UnifiedExposureRecord) ∈
        leftPrior := by
    simpa [priorExact] using rightMember
  have recordExact :
      (.machineFresh leftActor queryInput leftAnswer : UnifiedExposureRecord) =
        .machineFresh rightActor queryInput rightAnswer :=
    List.inj_on_of_nodup_map (exact_root_record_causal_inputs_nodup input)
      (leftPrefixMember _ leftMember) (leftPrefixMember _ rightMember') rfl
  injection recordExact

#print axioms exact_equal_root_priors_same_input_answer_eq

end

end AspisK1.V7Tag73ExactPairPriorInputUniqueness
