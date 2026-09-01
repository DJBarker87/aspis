import AspisFormal.K1.V7Tag73ExactFixedCleanQ16ProfileInvariant
import AspisFormal.K1.V7Tag73ExactRootQueryCausalOrder

/-!
# Causal chronology of an adversary-owned final-work anchor

An adversary may legitimately be the first caller of a final-work input.  The
security-relevant fact is instead chronological: the 256-bit transcript state
serialized into that input cannot be an oracle answer produced later in the
same target-clean root execution.  Otherwise that later answer would equal a
literal state prefix already present in its query history, contradicting the
exact causal-target certificate.

This module proves that fact separately for later adversary queries and for
all verifier-root queries.  It neither classifies raw SHA inputs by protocol
role nor treats adversary-first exposure itself as a bad event.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAdversaryAnchorPrefinalChronology

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedCleanQ16ProfileInvariant
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootQueryCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A query whose literal state prefix is `laterAnswer` cannot precede the
adversary query that freshly produces `laterAnswer`. -/
theorem exact_root_adversary_prefix_cannot_reference_later_adversary_answer
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (prior between later : List (ShaInput × Digest256))
    (anchorInput producerInput : ShaInput)
    (anchorAnswer laterAnswer : Digest256)
    (decomposition :
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
        prior ++ (anchorInput, anchorAnswer) ::
          between ++ (producerInput, laterAnswer) :: later)
    (statePrefix : HasLiteralStatePrefix laterAnswer anchorInput) : False := by
  have producerDecomposition :
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
        (prior ++ (anchorInput, anchorAnswer) :: between) ++
          (producerInput, laterAnswer) :: later := by
    simpa only [List.cons_append, List.append_assoc] using decomposition
  have avoids := exact_root_adversary_answer_avoids_prior_query_prefixes
    transitionRoom input
      (prior ++ (anchorInput, anchorAnswer) :: between) producerInput
      laterAnswer later producerDecomposition
  exact avoids (anchorInput, anchorAnswer) (by simp) statePrefix

/-- A verifier-root answer cannot equal the literal state prefix of any
earlier adversary query. -/
theorem exact_root_adversary_prefix_cannot_reference_verifier_answer
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (anchorInput : ShaInput) (anchorAnswer : Digest256)
    (anchorMember : (anchorInput, anchorAnswer) ∈
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries)
    (verifierPrior verifierLater : List (ShaInput × Digest256))
    (producerInput : ShaInput) (laterAnswer : Digest256)
    (decomposition :
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        verifierPrior ++ (producerInput, laterAnswer) :: verifierLater)
    (statePrefix : HasLiteralStatePrefix laterAnswer anchorInput) : False := by
  have avoids := exact_root_verifier_answer_avoids_prior_query_prefixes
    transitionRoom input verifierPrior producerInput laterAnswer verifierLater
      decomposition
  exact avoids.1 (anchorInput, anchorAnswer) anchorMember statePrefix

/-- The pre-final transcript state carried by an adversary-owned selected
anchor is not produced after that anchor in the adversary segment and is not
produced anywhere in the later verifier segment.  The returned existential
retains the exact source position of the anchor for the subsequent
semantic-profile commitment proof. -/
theorem exact_fixed_k13_adversary_anchor_prefinal_is_not_later_root_answer
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (trial : ExactCompilerExposureTrial parameters)
    (witness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder sample trial)
    (anchor : ExactFixedK13AdversaryAnchor witness.input trial) :
    ∃ queryPrior queryLater anchorInput anchorAnswer digest,
      witness.input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
          queryPrior ++ (anchorInput, anchorAnswer) :: queryLater ∧
      HasLiteralStatePrefix digest anchorInput ∧
      ExactOperationalPrefinalDigest witness.input digest ∧
      (anchorInput =
          (literalFinalWorkKey digest
            (exactOperationalTape witness.input).messages.finalGrinding.selected).workInput ∨
        anchorInput =
          (literalFinalWorkKey digest
            (exactOperationalTape witness.input).messages.finalGrinding.selected).absorbInput) ∧
      (∀ between producerInput producerLater,
        witness.input.package.root.full.projection.rootPrefixes.adversary.freshQueries ≠
          queryPrior ++ (anchorInput, anchorAnswer) ::
            between ++ (producerInput, digest) :: producerLater) ∧
      (∀ verifierPrior producerInput verifierLater,
        witness.input.package.root.full.projection.rootPrefixes.verifier.freshQueries ≠
          verifierPrior ++ (producerInput, digest) :: verifierLater) := by
  obtain ⟨rootPrior, rootLater, anchorInput, anchorAnswer, digest, rootExact,
      _trialExact, statePrefix, prefinalOrigin, anchorKind⟩ :=
    exact_fixed_k13_adversary_anchor_has_prefinal_digest_prefix trial witness
      anchor
  obtain ⟨queryPrior, queryLater, adversaryExact, _rootPriorExact⟩ :=
    exact_fixed_k13_adversary_anchor_has_literal_adversary_prefix witness.input
      rootPrior rootLater anchorInput anchorAnswer rootExact
  refine ⟨queryPrior, queryLater, anchorInput, anchorAnswer, digest,
    adversaryExact, statePrefix, prefinalOrigin, anchorKind, ?_, ?_⟩
  · intro between producerInput producerLater laterExact
    exact exact_root_adversary_prefix_cannot_reference_later_adversary_answer
      transitionRoom witness.input queryPrior between producerLater anchorInput
        producerInput anchorAnswer digest laterExact statePrefix
  · intro verifierPrior producerInput verifierLater laterExact
    exact exact_root_adversary_prefix_cannot_reference_verifier_answer
      transitionRoom witness.input anchorInput anchorAnswer (by
        rw [adversaryExact]
        simp) verifierPrior verifierLater producerInput digest laterExact
          statePrefix

#print axioms
  exact_root_adversary_prefix_cannot_reference_later_adversary_answer
#print axioms exact_root_adversary_prefix_cannot_reference_verifier_answer
#print axioms
  exact_fixed_k13_adversary_anchor_prefinal_is_not_later_root_answer

end

end AspisK1.V7Tag73ExactAdversaryAnchorPrefinalChronology
