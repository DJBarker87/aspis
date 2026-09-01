import AspisFormal.K1.V7Tag73ExactFixedCleanQ16ProfileInvariant
import AspisFormal.K1.V7Tag73ExactDagCandidateLabeledRootRouting
import AspisFormal.K1.V7Tag73ExactRootLookupCausalOrder
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
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedCleanQ16ProfileInvariant
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73ExactFinalWorkPairRootOrder
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactRootQueryCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

@[simp] theorem machine_fresh_record_mem_projected_iff
    (actor : QueryActor) (queries : List (ShaInput × Digest256))
    (input : ShaInput) (answer : Digest256) :
    (.machineFresh actor input answer : UnifiedExposureRecord) ∈
        projectedMachineFreshRecords actor queries ↔
      (input, answer) ∈ queries := by
  induction queries with
  | nil => simp [projectedMachineFreshRecords]
  | cons query queries ih =>
      rcases query with ⟨queryInput, queryAnswer⟩
      simp [projectedMachineFreshRecords, ih]

@[simp] theorem projected_machine_fresh_records_length
    (actor : QueryActor) (queries : List (ShaInput × Digest256)) :
    (projectedMachineFreshRecords actor queries).length = queries.length := by
  induction queries with
  | nil => rfl
  | cons query queries ih =>
      rcases query with ⟨input, answer⟩
      simp [projectedMachineFreshRecords, ih]

/-- Projecting an actor label onto a fresh-query sequence preserves and
reflects duplicate-freedom. -/
theorem projected_machine_fresh_records_nodup_iff
    (actor : QueryActor) (queries : List (ShaInput × Digest256)) :
    (projectedMachineFreshRecords actor queries).Nodup ↔ queries.Nodup := by
  induction queries with
  | nil => simp [projectedMachineFreshRecords]
  | cons query queries ih =>
      rcases query with ⟨input, answer⟩
      simp [projectedMachineFreshRecords, ih,
        machine_fresh_record_mem_projected_iff]

/-- In a duplicate-free chronological trace, two decompositions around the
same pivot have the same prefix. -/
theorem nodup_equal_pivot_prefixes
    {Record : Type} [DecidableEq Record]
    (pivot : Record) :
    ∀ leftPrior leftLater rightPrior rightLater : List Record,
      (leftPrior ++ pivot :: leftLater).Nodup →
      leftPrior ++ pivot :: leftLater =
        rightPrior ++ pivot :: rightLater →
      leftPrior = rightPrior := by
  intro leftPrior
  induction leftPrior with
  | nil =>
      intro leftLater rightPrior rightLater nodup exact
      cases rightPrior with
      | nil => rfl
      | cons rightHead rightTail =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at exact
          rcases exact with ⟨rfl, tailExact⟩
          have rightNodup :
              (pivot :: rightTail ++ pivot :: rightLater).Nodup := by
            simpa [tailExact] using nodup
          simp at rightNodup
  | cons leftHead leftTail ih =>
      intro leftLater rightPrior rightLater nodup exact
      cases rightPrior with
      | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at exact
          rcases exact with ⟨rfl, _tailExact⟩
          simp at nodup
      | cons rightHead rightTail =>
          simp only [List.cons_append, List.cons.injEq] at exact
          rcases exact with ⟨rfl, tailSequenceExact⟩
          have tailNodup :
              (leftTail ++ pivot :: leftLater).Nodup := nodup.of_cons
          have tailExact : leftTail = rightTail :=
            ih leftLater rightTail rightLater tailNodup tailSequenceExact
          simp [tailExact]

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
      trial.val = queryPrior.length ∧
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
  obtain ⟨rootPrior, rootLater, anchorInput, anchorAnswer, digest, _base,
      _absorbActor, rootExact, trialExact, statePrefix, prefinalOrigin,
      anchorKind, _baseExact, _absorbMember⟩ :=
    exact_fixed_k13_adversary_anchor_has_prefinal_digest_prefix trial witness
      anchor
  obtain ⟨queryPrior, queryLater, adversaryExact, rootPriorExact⟩ :=
    exact_fixed_k13_adversary_anchor_has_literal_adversary_prefix witness.input
      rootPrior rootLater anchorInput anchorAnswer rootExact
  refine ⟨queryPrior, queryLater, anchorInput, anchorAnswer, digest,
    adversaryExact, ?_, statePrefix, prefinalOrigin, anchorKind, ?_, ?_⟩
  · rw [rootPriorExact] at trialExact
    simpa only [projected_machine_fresh_records_length] using trialExact
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

/-- The `final256` query producing the selected pre-final digest occurs
strictly before an adversary-owned final-work anchor in the literal adversary
query list.  This is the commitment point needed by the remaining semantic
profile proof: it neither classifies a raw coordinate nor charges a normal
adversary prequery as a bad event. -/
theorem exact_fixed_k13_adversary_anchor_has_earlier_final256_producer
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
    ∃ producerPrior middle anchorLater producerInput anchorInput
        anchorAnswer digest,
      witness.input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
        producerPrior ++ (producerInput, digest) ::
          middle ++ (anchorInput, anchorAnswer) :: anchorLater ∧
      trial.val =
        (producerPrior ++ (producerInput, digest) :: middle).length ∧
      tableLookup (exactOperationalTable witness.input) producerInput =
        some digest ∧
      HasLiteralStatePrefix digest anchorInput ∧
      ExactOperationalPrefinalDigest witness.input digest := by
  obtain ⟨queryPrior, queryLater, anchorInput, anchorAnswer, digest,
      adversaryExact, trialExact, statePrefix, prefinalOrigin, _anchorKind,
      notLaterAdversary, notVerifier⟩ :=
    exact_fixed_k13_adversary_anchor_prefinal_is_not_later_root_answer
      transitionRoom trial witness anchor
  obtain ⟨beforeFinal256, producerLookup⟩ := prefinalOrigin
  let producerInput : ShaInput :=
    bytes beforeFinal256.digest ++
      [domAbsorb,
        (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape witness.input).messages.finalValues).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape witness.input).messages.finalValues).data
  have producerPosition :=
    exact_compiler_final_lookup_has_root_position witness.input
      producerInput digest (by simpa [producerInput] using producerLookup)
  rcases producerPosition with
      ⟨producerPrior, producerLater, producerAdversary⟩ |
      ⟨verifierPrior, verifierLater, producerVerifier⟩
  · have producerMember : (producerInput, digest) ∈
        witness.input.package.root.full.projection.rootPrefixes.adversary.freshQueries :=
      by rw [producerAdversary]; simp
    have anchorMember : (anchorInput, anchorAnswer) ∈
        witness.input.package.root.full.projection.rootPrefixes.adversary.freshQueries := by
      rw [adversaryExact]
      simp
    have distinct : (producerInput, digest) ≠ (anchorInput, anchorAnswer) := by
      intro equal
      have inputExact : producerInput = anchorInput := congrArg Prod.fst equal
      have avoids := exact_compiler_final_lookup_answer_avoids_own_input
        witness.input producerInput digest (by
          simpa [producerInput] using producerLookup)
      apply avoids
      simpa [inputExact] using statePrefix
    rcases distinct_members_have_strict_list_order
        witness.input.package.root.full.projection.rootPrefixes.adversary.freshQueries
        (producerInput, digest) (anchorInput, anchorAnswer) distinct
        producerMember anchorMember with producerFirst | anchorFirst
    · obtain ⟨producerPrior, middle, anchorLater, exact⟩ := producerFirst
      have rootRecordsNodup :
          (exactFixedRootRecords witness.input.package.root).Nodup :=
        List.Nodup.of_map UnifiedExposureRecord.answer
          (exact_root_record_answers_nodup witness.input)
      have adversaryRecordsNodup :
          (projectedMachineFreshRecords .adversary
            witness.input.package.root.full.projection.rootPrefixes.adversary.freshQueries).Nodup := by
        unfold exactFixedRootRecords fullProjectedRootRecords at rootRecordsNodup
        exact (List.nodup_append.mp rootRecordsNodup).1
      have adversaryNodup :
          witness.input.package.root.full.projection.rootPrefixes.adversary.freshQueries.Nodup :=
        (projected_machine_fresh_records_nodup_iff .adversary _).mp
          adversaryRecordsNodup
      have queryPriorExact :
          queryPrior = producerPrior ++ (producerInput, digest) :: middle :=
        nodup_equal_pivot_prefixes (anchorInput, anchorAnswer)
          queryPrior queryLater
          (producerPrior ++ (producerInput, digest) :: middle) anchorLater
          (by simpa [adversaryExact] using adversaryNodup)
          (adversaryExact.symm.trans (by
            simpa only [List.cons_append, List.append_assoc] using exact))
      exact ⟨producerPrior, middle, anchorLater, producerInput, anchorInput,
        anchorAnswer, digest, exact, by simpa [queryPriorExact] using trialExact,
        by simpa [producerInput] using producerLookup, statePrefix,
        ⟨beforeFinal256, producerLookup⟩⟩
    · obtain ⟨beforeAnchor, middle, producerLater, exact⟩ := anchorFirst
      exfalso
      exact exact_root_adversary_prefix_cannot_reference_later_adversary_answer
        transitionRoom witness.input beforeAnchor middle producerLater
          anchorInput producerInput anchorAnswer digest exact statePrefix
  · exfalso
    exact notVerifier verifierPrior producerInput verifierLater producerVerifier

/-- Root-record form of the preceding chronology theorem.  It keeps the
literal producer and anchor in one exact combined-root decomposition, which
lets cross-fibre replay transport the already-created `final256` coordinate. -/
theorem exact_fixed_k13_adversary_anchor_has_earlier_final256_root_record
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
    ∃ rootPrior rootMiddle rootLater producerInput anchorInput anchorAnswer
        digest,
      exactFixedRootRecords witness.input.package.root =
        rootPrior ++
          (.machineFresh .adversary producerInput digest :
            UnifiedExposureRecord) :: rootMiddle ++
          (.machineFresh .adversary anchorInput anchorAnswer :
            UnifiedExposureRecord) :: rootLater ∧
      trial.val =
        (rootPrior ++
          (.machineFresh .adversary producerInput digest :
            UnifiedExposureRecord) :: rootMiddle).length ∧
      tableLookup (exactOperationalTable witness.input) producerInput =
        some digest ∧
      HasLiteralStatePrefix digest anchorInput ∧
      ExactOperationalPrefinalDigest witness.input digest := by
  obtain ⟨producerPrior, middle, anchorLater, producerInput, anchorInput,
      anchorAnswer, digest, adversaryExact, trialExact, producerLookup,
      statePrefix, prefinalOrigin⟩ :=
    exact_fixed_k13_adversary_anchor_has_earlier_final256_producer
      transitionRoom trial witness anchor
  refine ⟨projectedMachineFreshRecords .adversary producerPrior,
    projectedMachineFreshRecords .adversary middle,
    projectedMachineFreshRecords .adversary anchorLater ++
    projectedMachineFreshRecords .verifier
        witness.input.package.root.full.projection.rootPrefixes.verifier.freshQueries,
    producerInput, anchorInput, anchorAnswer, digest, ?_, ?_, producerLookup,
    statePrefix, prefinalOrigin⟩
  · unfold exactFixedRootRecords fullProjectedRootRecords
    rw [adversaryExact]
    simp only [projected_machine_fresh_records_append,
      projectedMachineFreshRecords, List.cons_append, List.append_assoc]
  · simpa only [List.length_append, List.length_cons,
      projected_machine_fresh_records_length] using trialExact

#print axioms
  exact_root_adversary_prefix_cannot_reference_later_adversary_answer
#print axioms projected_machine_fresh_records_nodup_iff
#print axioms nodup_equal_pivot_prefixes
#print axioms exact_root_adversary_prefix_cannot_reference_verifier_answer
#print axioms
  exact_fixed_k13_adversary_anchor_prefinal_is_not_later_root_answer
#print axioms
  exact_fixed_k13_adversary_anchor_has_earlier_final256_producer
#print axioms
  exact_fixed_k13_adversary_anchor_has_earlier_final256_root_record

end

end AspisK1.V7Tag73ExactAdversaryAnchorPrefinalChronology
