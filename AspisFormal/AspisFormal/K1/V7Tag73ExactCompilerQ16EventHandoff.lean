import AspisFormal.K1.V7Tag73ExactCompilerQ16DuplexForest
import AspisFormal.K1.V7Tag73ExactFixedK13K14Classifier
import AspisFormal.K1.V7Tag73ExactParsedProofSourceBinding
import AspisFormal.K1.V7Tag73OperationalQ16ForestHandoff

/-!
# Exact compiler q16 event handoff

The canonical duplex forest reconstructed from the accepted production run
realizes that run's literal first-cap-203 search.  Consequently a concrete
K1.3 query-phase failure puts the selected operational schedule in the exact
successful-forest bad event for its pre-q16 consistency set.

This file is deterministic.  It neither assumes verifier-first oracle queries
nor claims the subsequent random-oracle coordinate factorization.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerQ16EventHandoff

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73SchedulerNativeQ16Replay
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73Q16DeployedDecoderPrefixBridge
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactCompilerQ16BranchCoordinates
open AspisK1.V7Tag73ExactCompilerQ16DuplexForest
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5WithoutReplacementQuerySoundness
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- The accepted source binding identifies the operationally selected q16
positions with the K1.3 query vector, so a query-phase failure places every
selected position in its exact consistency set. -/
theorem exact_query_phase_failure_selected_all_in_bad
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

/-- The canonical source-derived output forest realizes exactly the literal
accepted search, including every earlier rejected candidate and the selected
cap-203 schedule. -/
theorem exact_operational_q16_duplex_forest_realizes_search
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
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions) :
    OperationalQ16ForestRealization
      (exactOperationalTape input).frontierNodes
      (exactOperationalTape input).search
      (exactOperationalQ16DuplexForest input).1 where
  decodedExact counter schedule beforeSelected outcomeExact := by
    let coordinates := exactOperationalQ16BranchCoordinates input counter
      beforeSelected
    let branch := schedulerNativeQ16BranchOfSpec
      (exactOperationalQ16InitialDigest input)
      { counter := counter
        outcome := (exactOperationalTape input).search.outcome counter }
    have pairsExact :
        q16BranchDuplexPairs branch (exactOperationalQ16DuplexForest input) =
          coordinates.outputs.zip coordinates.advances := by
      simpa [branch, coordinates] using
        exact_operational_q16_branch_duplex_pairs input counter beforeSelected
    have outputsExact :
        q16BranchOutputBlocks branch (exactOperationalQ16DuplexForest input) =
          coordinates.outputs := by
      unfold q16BranchOutputBlocks
      rw [pairsExact]
      apply List.ext_getElem
      · rw [List.length_map, List.length_zip, coordinates.advancesLength,
          Nat.min_self]
      · intro index leftBound rightBound
        rw [List.getElem_map, List.getElem_zip]
    have decodedSchedule :
        decodeCandidateOutcome counter
            (q16BranchOutputBlocks branch
              (exactOperationalQ16DuplexForest input)) =
          some (.schedule schedule) := by
      rw [outputsExact, coordinates.decoded, outcomeExact]
    apply decodeCandidateOutcome_schedule_to_q16CandidateOutput counter
      ((exactOperationalQ16DuplexForest input).1 counter)
      (q16BranchOutputBlocks branch (exactOperationalQ16DuplexForest input))
      schedule
    · simpa [branch, schedulerNativeQ16BranchOfSpec, outcomeExact,
        CandidateOutcome.blocksUsed] using
          q16_branch_output_blocks_eq_take branch
            (exactOperationalQ16DuplexForest input)
    · exact decodedSchedule
  frontierExact counter schedule _beforeSelected _outcomeExact :=
    (frontierExact schedule).symm

/-- A concrete K1.3 query failure is in the exact finite bad event of the
canonical successful q16 forest.  This closes the semantic event mapping; it
does not yet identify those forest coordinates with a uniform ROM-tape
factor. -/
theorem exact_query_phase_failure_implies_q16_successful_bad_event
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
      (exactK13ParsedProof input).queries)
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions) :
    successfulQ16DigestForestEquiv
        ⟨(exactOperationalQ16DuplexForest input).1,
          exact_operational_q16_duplex_forest_succeeds input frontierExact⟩ ∈
      q16SuccessfulCoordinatesBadEvent
        (consistencySet (exactK13ParsedProof input).schedule
          (exactK13Encoders decoder) (exactK13Transcript input k12)) := by
  apply operational_all_in_bad_implies_successful_coordinate_bad
    (exact_operational_q16_duplex_forest_realizes_search input frontierExact)
  exact exact_query_phase_failure_selected_all_in_bad source failure

#print axioms exact_query_phase_failure_selected_all_in_bad
#print axioms exact_operational_q16_duplex_forest_realizes_search
#print axioms exact_query_phase_failure_implies_q16_successful_bad_event

end

end AspisK1.V7Tag73ExactCompilerQ16EventHandoff
