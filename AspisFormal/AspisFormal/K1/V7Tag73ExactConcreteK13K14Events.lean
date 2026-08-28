import AspisFormal.K1.V7Tag73ExactConcreteStageAssembly
import AspisFormal.K1.V7Tag73ExactFixedK13K14FailureReduction
import AspisFormal.K1.V7Tag73ExactParsedProofSourceBinding
import AspisFormal.K1.V7Tag73ExactOneFoldEncoderBinding
import AspisFormal.K1.V7Tag73ExactOneFoldRestorationStrategy
import AspisFormal.K1.V7ExactCorrelatedAgreementTerminal
import AspisFormal.K1.V7Tag73JointQueryBatchSoundness
import AspisFormal.K1.V7Tag73Q16FirstCompactUniformity
import AspisFormal.Pool.V7RelationCandidateBinding

/-!
# Concrete K1.3/K1.4 events for the assembled Tag-73 stages

This module removes the generic K1.3 and K1.4 error families from the K1.6
stage package.  Under the exact successful one-fold verifier check and the
proved production initial-encoder identity, an executable K1.3 error is
covered by q16 proximity failure, the published one-fold event, the repaired
joint degree-sixteen query/relation collision, or a later degree-six relation
repair.  An executable K1.4 error is literally the published width-29
correlated-agreement event.

The events remain separate so the q16 probability theorem and the published
circle-code theorem can be instantiated without double counting.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactConcreteK13K14Events

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactOneFoldRestorationStrategy
open AspisK1.V7ExactCorrelatedAgreementTerminal
open AspisK1.V7Tag73JointQueryBatchSoundness
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactConcreteStageAssembly
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7RelationCandidateBinding
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriRelationCandidateBridge
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction
open AspisV6PublishedTheoremInterfaces
open AspisV6QueryBatchSoundness

noncomputable section

/-- The sixteen disclosed-final evaluations installed by the exact Tag-73
query-batch covector. -/
def exactTag73K13ExpectedQueryVector
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input) : QueryVector QM31Exact :=
  fun ordinal =>
    (exactK13Encoders decoder).final
      (exactK13Transcript input k12).disclosedFinal
      ((exactK13ParsedProof input).queries ordinal)

/-- The sixteen values authenticated from the two truncated Merkle trees and
folded once with the exact selected alpha. -/
def exactTag73K13AuthenticatedQueryVector
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input) : QueryVector QM31Exact :=
  fun ordinal =>
    circleFoldLayer 262144 (exactK13ParsedProof input).schedule.alpha
      (exactK13ParsedProof input).schedule.circleInv2x
      (exactK13ParsedProof input).schedule.circleInv2y
      (exactK13Transcript input k12).initial
      ((exactK13ParsedProof input).queries ordinal)

/-- Pointwise ideal acceptance is exactly equality of the two concrete
sixteen-vectors. This theorem is used only after excluding the deployed
degree-at-most-15 batching collision. -/
theorem exactTag73K13IdealAccepts_iff_query_vectors_eq
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input) :
    IdealAccepts (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12)
        (exactK13ParsedProof input).queries ↔
      exactTag73K13ExpectedQueryVector decoder input k12 =
        exactTag73K13AuthenticatedQueryVector decoder input k12 := by
  constructor
  · intro accepts
    funext ordinal
    simpa [exactTag73K13ExpectedQueryVector,
      exactTag73K13AuthenticatedQueryVector, QueryConsistent] using
        (accepts ordinal).symm
  · intro equal ordinal
    have atOrdinal := congrFun equal ordinal
    simpa [exactTag73K13ExpectedQueryVector,
      exactTag73K13AuthenticatedQueryVector, QueryConsistent] using
        atOrdinal.symm

/-- Per-run relation data and exact source facts needed by the corrected K1.3
handoff.  The source supplies the literal candidate execution, identifies its
post-query discrepancy with the repaired shifted batch, and exposes the
accepted terminal comparison.  It does not assume pointwise `IdealAccepts`
or that a standalone query residual vanishes. -/
structure ExactTag73K13SourceObligations
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Type where
  execution :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample),
      CandidateExecution QM31Exact
  preQueryDiscrepancy :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample),
      QM31Exact
  preQueryDiscrepancyExact :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample),
      preQueryDiscrepancy sample input =
        (execution sample input).claimAfterRound0 -
          candidateClaim (execution sample input).foldedOodWeights256
            (execution sample input).disclosedFinal256
  beforeOneExact :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input),
      (execution sample input).discrepancyTrace.before 1 =
        jointQueryBatchDiscrepancy
          (preQueryDiscrepancy sample input)
          (exactTag73K13ExpectedQueryVector decoder input k12)
          (exactTag73K13AuthenticatedQueryVector decoder input k12)
          (exactOperationalChallenge input .queryBatch)
  relationTerminal :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample),
      (execution sample input).RelationTerminalAccepts
  alphaExact :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (round : Fin 4),
      (execution sample input).alpha round =
        exactOperationalChallenge input (.alpha round)

/-- Exact K1.3 residual event after deterministic source failures and the
impossible list-cap branch are removed. -/
def exactTag73K13QueryOrOneFoldEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input),
    QueryPhaseFailure (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12)
        (exactK13ParsedProof input).queries ∨
      OneFoldReductionFailure (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12)}

/-- The q16 half of the exact K1.3 residual event.  Keeping this as its own
set lets the finite first-cap-203 theorem be applied without charging the
one-fold event a second time. -/
def exactTag73K13QueryEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input),
    QueryPhaseFailure (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries}

/-- The published one-fold half of the exact K1.3 residual event. -/
def exactTag73K13OneFoldEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input),
    OneFoldReductionFailure (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)}

/-- Unequal pointwise vectors whose repaired joint discrepancy vanishes at
the deployed nonzero `rho`.  The preceding relation scalar is part of the
same polynomial, so this event has degree at most sixteen. -/
def exactTag73K13JointQueryBatchCollisionEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input),
    exactTag73K13ExpectedQueryVector decoder input k12 ≠
        exactTag73K13AuthenticatedQueryVector decoder input k12 ∧
      exactOperationalChallenge input .queryBatch ∈
        jointQueryBatchNonzeroCollisionSet
          (source.preQueryDiscrepancy sample input)
          (exactTag73K13ExpectedQueryVector decoder input k12)
          (exactTag73K13AuthenticatedQueryVector decoder input k12)}

/-- If the repaired joint discrepancy survives query injection but the final
relation comparison accepts, one of the three later alpha challenges repaired
it through a degree-six collision. -/
def exactTag73K13LaterRelationAlphaEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input)
      (round : Fin 4),
    0 < round.val ∧
      (source.execution sample input).discrepancyTrace.AlphaRepair round}

/-- Complete corrected K1.3 event.  A failed pointwise classifier is charged
to the joint degree-sixteen `rho` collision or, if its discrepancy survives,
to a later degree-six relation-alpha repair. -/
def exactTag73K13CompleteEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  ((exactTag73K13QueryEvent transitionFuel configuration projection
        fixedInstance decoder ∪
      exactTag73K13OneFoldEvent transitionFuel configuration projection
        fixedInstance decoder) ∪
    exactTag73K13JointQueryBatchCollisionEvent transitionFuel configuration
      projection fixedInstance decoder source) ∪
    exactTag73K13LaterRelationAlphaEvent transitionFuel configuration
      projection fixedInstance decoder source

/-- The executable K1.3 residual splits exactly into the two events to which
the independent q16 and published one-fold bounds are applied. -/
theorem exactTag73K13QueryOrOneFoldEvent_eq_union
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    exactTag73K13QueryOrOneFoldEvent transitionFuel configuration projection
        fixedInstance decoder =
      exactTag73K13QueryEvent transitionFuel configuration projection
          fixedInstance decoder ∪
        exactTag73K13OneFoldEvent transitionFuel configuration projection
          fixedInstance decoder := by
  ext sample
  constructor
  · rintro ⟨input, k12, query | oneFold⟩
    · exact Or.inl ⟨input, k12, query⟩
    · exact Or.inr ⟨input, k12, oneFold⟩
  · rintro (⟨input, k12, query⟩ | ⟨input, k12, oneFold⟩)
    · exact ⟨input, k12, Or.inl query⟩
    · exact ⟨input, k12, Or.inr oneFold⟩

/-- Exact K1.4 residual event exposed directly by its sole classifier error
constructor. -/
def exactTag73K14Width29Event
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input)
      (_k13 : ExactK13Certificate decoder input k12),
    Width29DecompositionFailure decoder k12.words
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule}

/-! ## Literal selected-schedule q16 target -/

/-- A fixed-run query failure says that the literal cap-203 schedule selected
by the operational transcript lies entirely in one exact consistency set of
size at most 9,557.  No probability or work normalization appears here. -/
theorem query_phase_failure_is_literal_selected_all_in_bad
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    {decoded : Fin 641 → QM31Exact}
    (source : ExactParsedProofSourceBinding input decoded)
    (failure : QueryPhaseFailure (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries) :
    AllInBad
      (consistencySet (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12))
      (exactOperationalTape input).search.selectedSchedule.positions := by
  intro ordinal
  have accepted := accepted_queries_mem_consistencySet
    (exactK13ParsedProof input).schedule (exactK13Encoders decoder)
    (exactK13Transcript input k12) (exactK13ParsedProof input).queries
    failure.1 ordinal
  rw [source.selectedQueriesExact] at accepted
  exact accepted

/-- Exact witness consumed by the forthcoming same-tape q16 coupling: one
pre-q16 consistency set, its deployed cardinality cap, and the actual selected
schedule landing wholly inside it. -/
theorem query_phase_failure_exposes_literal_q16_bad_set
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    {decoded : Fin 641 → QM31Exact}
    (source : ExactParsedProofSourceBinding input decoded)
    (failure : QueryPhaseFailure (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries) :
    ∃ bad : Finset (Fin 262144),
      bad.card ≤ 9557 ∧
        AllInBad bad
          (exactOperationalTape input).search.selectedSchedule.positions := by
  exact ⟨consistencySet (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12), failure.2,
    query_phase_failure_is_literal_selected_all_in_bad source failure⟩

/-! ## Exact internally proved one-fold target -/

/-- A concrete K1.3 one-fold failure is charged to one fixed pre-alpha bad
set of size at most the release degree-three cap.  The sampled alpha is
also identified with the literal operational transcript challenge. -/
theorem onefold_failure_exposes_exact_published_bad_set
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    {decoded : Fin 641 → QM31Exact}
    (source : ExactParsedProofSourceBinding input decoded)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (failure : OneFoldReductionFailure (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)) :
    let binding := exactOneFoldAlgebraBinding
      (exactK13ParsedProof input).schedule (exactK13Encoders decoder)
      initialEncoderExact finalEncoderExact source.inverseTablesExact
    (exactK13ParsedProof input).schedule.alpha =
        exactOperationalChallenge input (.alpha 0) ∧
      (exactK13ParsedProof input).schedule.alpha ∈
        oneFoldBadChallenges (exactK13ParsedProof input).schedule
          (exactK13Encoders decoder) binding (exactK13Transcript input k12) ∧
      (oneFoldBadChallenges (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) binding
        (exactK13Transcript input k12)).card ≤ foldChallengeCap := by
  dsimp only
  refine ⟨source.alphaZeroExact, ?_⟩
  have publishedForBinding : PublishedOneFoldCurveDecodability
      (exactOneFoldAlgebraBinding (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) initialEncoderExact finalEncoderExact
        source.inverseTablesExact).finalLinear := by
    change PublishedOneFoldCurveDecodability exactFinalLinear
    exact exactV7FinalPublishedOneFoldCurveDecodability
  exact oneFoldReductionFailure_has_published_cap
    (exactK13ParsedProof input).schedule (exactK13Encoders decoder)
    (exactOneFoldAlgebraBinding (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) initialEncoderExact finalEncoderExact
      source.inverseTablesExact)
    (exactK13Transcript input k12) publishedForBinding failure

/-- If the executable pointwise classifier rejects, literal source acceptance
forces one of exactly two outcomes: the repaired joint polynomial vanishes at
the deployed `rho`, or its nonzero post-query discrepancy is repaired by one
of the three later relation challenges. -/
theorem ideal_rejected_exposes_joint_or_later_relation_collision
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {k12 : ExactPrefixK12Certificate input}
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder)
    (rejected : ¬ IdealAccepts (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)
      (exactK13ParsedProof input).queries) :
    (exactTag73K13ExpectedQueryVector decoder input k12 ≠
          exactTag73K13AuthenticatedQueryVector decoder input k12 ∧
        exactOperationalChallenge input .queryBatch ∈
          jointQueryBatchNonzeroCollisionSet
            (source.preQueryDiscrepancy sample input)
            (exactTag73K13ExpectedQueryVector decoder input k12)
            (exactTag73K13AuthenticatedQueryVector decoder input k12)) ∨
      ∃ round : Fin 4, 0 < round.val ∧
        (source.execution sample input).discrepancyTrace.AlphaRepair
          round := by
  have different : exactTag73K13ExpectedQueryVector decoder input k12 ≠
      exactTag73K13AuthenticatedQueryVector decoder input k12 := by
    intro equal
    exact rejected
      ((exactTag73K13IdealAccepts_iff_query_vectors_eq decoder input k12).2
        equal)
  have rhoNonzero : exactOperationalChallenge input .queryBatch ≠ 0 :=
    (exact_operational_input_constructs_post_eta_nonzero_challenges input).2.2
  exact joint_collision_or_later_alphaRepair
      (source.execution sample input)
      (source.preQueryDiscrepancy sample input)
      (exactTag73K13ExpectedQueryVector decoder input k12)
      (exactTag73K13AuthenticatedQueryVector decoder input k12)
      (exactOperationalChallenge input .queryBatch) rhoNonzero different
      (source.beforeOneExact sample input k12)
      (source.relationTerminal sample input)

/-- Every executable K1.3 error is covered by q16, published one-fold, joint
rho, or later relation-alpha collision events. -/
theorem assembled_k13_error_subset_complete
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) :
    k13CircleListDecodeErrorEvent
        (exactTag73ProofRelevantStages transitionFuel configuration projection
          fixedInstance relation decoder decoderBinding k15) ⊆
      exactTag73K13CompleteEvent transitionFuel configuration projection
        fixedInstance decoder source := by
  intro sample member
  rcases member with ⟨input, k12, error⟩
  rcases error with ⟨error⟩
  change sample ∈
    ((exactTag73K13QueryEvent transitionFuel configuration projection
          fixedInstance decoder ∪
        exactTag73K13OneFoldEvent transitionFuel configuration projection
          fixedInstance decoder) ∪
      exactTag73K13JointQueryBatchCollisionEvent transitionFuel configuration
        projection fixedInstance decoder source) ∪
      exactTag73K13LaterRelationAlphaEvent transitionFuel configuration
        projection fixedInstance decoder source
  cases error with
  | idealRejected rejected =>
      rcases ideal_rejected_exposes_joint_or_later_relation_collision source
        rejected with joint | later
      · exact Or.inl (Or.inr ⟨input, k12, joint⟩)
      · rcases later with ⟨round, positive, repair⟩
        exact Or.inr ⟨input, k12, round, positive, repair⟩
  | queryPhaseFailure failure =>
      exact Or.inl (Or.inl (Or.inl ⟨input, k12, failure⟩))
  | oneFoldReductionFailure failure =>
      exact Or.inl (Or.inl (Or.inr ⟨input, k12, failure⟩))
  | initialListCapFailure failure =>
      exact False.elim
        ((exact_k13_initial_list_cap_failure_impossible decoder
          initialEncoderExact input k12) failure)

theorem assembled_k14_error_subset_width29
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding) :
    k14CoherentChainErrorEvent
        (exactTag73ProofRelevantStages transitionFuel configuration projection
          fixedInstance relation decoder decoderBinding k15) ⊆
      exactTag73K14Width29Event transitionFuel configuration projection
        fixedInstance decoder := by
  intro sample member
  rcases member with ⟨input, k12, k13, error⟩
  exact ⟨input, k12, k13,
    exact_k14_error_is_width29_failure error.some⟩

/-- Combined deterministic cover retained only for final union accounting;
the two branches remain individually available for their different bounds. -/
theorem assembled_k13_k14_error_subset_exact_union
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) :
    k13CircleListDecodeErrorEvent
          (exactTag73ProofRelevantStages transitionFuel configuration projection
            fixedInstance relation decoder decoderBinding k15) ∪
        k14CoherentChainErrorEvent
          (exactTag73ProofRelevantStages transitionFuel configuration projection
            fixedInstance relation decoder decoderBinding k15) ⊆
      exactTag73K13CompleteEvent transitionFuel configuration projection
          fixedInstance decoder source ∪
        exactTag73K14Width29Event transitionFuel configuration projection
          fixedInstance decoder := by
  intro sample member
  rcases member with k13Error | k14Error
  · exact Or.inl (assembled_k13_error_subset_complete transitionFuel
      configuration projection fixedInstance relation decoder decoderBinding
      k15 initialEncoderExact source k13Error)
  · exact Or.inr (assembled_k14_error_subset_width29 transitionFuel
      configuration projection fixedInstance relation decoder decoderBinding
      k15 k14Error)

#print axioms ideal_rejected_exposes_joint_or_later_relation_collision
#print axioms assembled_k13_error_subset_complete
#print axioms assembled_k14_error_subset_width29
#print axioms assembled_k13_k14_error_subset_exact_union
#print axioms query_phase_failure_is_literal_selected_all_in_bad
#print axioms query_phase_failure_exposes_literal_q16_bad_set
#print axioms onefold_failure_exposes_exact_published_bad_set
#print axioms exactTag73K13QueryOrOneFoldEvent_eq_union

end

end AspisK1.V7Tag73ExactConcreteK13K14Events
