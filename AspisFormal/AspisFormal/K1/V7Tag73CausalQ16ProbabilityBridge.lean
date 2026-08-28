import AspisFormal.K1.V7Tag73CausalQ16CoordinateRouter
import AspisFormal.K1.V7Tag73OperationalQ16ForestHandoff
import AspisFormal.K1.V7Tag73Q16SuccessfulForestBridge

/-!
# Causal q16 coordinates imply the exact semantic probability bound

The deployed q16 coordinates do not occupy a static prefix of the compiler
tape.  Their chronological locations may depend on earlier random-oracle
answers.  `CausalSlotRouter` expresses exactly the permitted dependence: the
destination of the current answer is selected before that answer is exposed,
while the continuation may depend on it.

This file connects such a router to the existing finite first-cap-203 q16
probability theorem.  Once the literal Tag-73 scheduler supplies the router
and the event-cover inclusion, no additional independence or iid premise is
needed.  The only remaining numerical bridge is the generated equality from
the semantic compact-frontier count to the frozen release integer.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73CausalQ16ProbabilityBridge

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73Q16CompilerTapeCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73Q16RawENNRealProbability
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev ExactCompilerQ16Residual
    (parameters : ExactCompilerResourceParameters) :=
  FreshAnswerTape Digest256
    ((exactCompilerTargetCaps parameters).length - 512)

/-- A complete online routing certificate for the exact compiler tape: all
512 q16 candidate/block slots are filled once, and every other exposure is
retained in the exact residual tape. -/
abbrev ExactCompilerCausalQ16Router
    (parameters : ExactCompilerResourceParameters) :=
  CausalSlotRouter Digest256 Q16DigestSlot Finset.univ
    ((exactCompilerTargetCaps parameters).length - 512)

/-- The adaptive router induces the coordinate equivalence expected by the
successful-q16 conditioning theorem. -/
def exactCompilerCausalQ16Coordinates
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalQ16Router parameters) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerQ16Residual parameters × Q16CandidateDigestForest := by
  let total := (exactCompilerTargetCaps parameters).length
  have enough : 512 ≤ total :=
    exact_compiler_tape_has_q16_coordinate_capacity parameters
  have totalEq : total = 512 + (total - 512) := by omega
  exact
    (Equiv.cast (congrArg (FreshAnswerTape Digest256) totalEq)).trans
      (router.q16CoordinateEquiv.trans
        (Equiv.prodComm Q16CandidateDigestForest
          (ExactCompilerQ16Residual parameters)))

/-- Pointwise deterministic cover used to discharge the probabilistic
theorem's `covered` premise.  Once the routed forest realizes the literal
first-cap-203 search and its selected schedule lies in the residual-dependent
bad set, the exact compiler coordinate pair is in the corresponding
successful-subtype event. -/
theorem operational_realization_covers_dependent_bad_coordinate
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalQ16Router parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (bad : Finset (Fin 262144))
    (realized : OperationalQ16ForestRealization frontierNodes search
      (exactCompilerCausalQ16Coordinates parameters router tape).2)
    (allBad : AllInBad bad
      (semanticScheduleOfOperational search.selectedSchedule)) :
    exactCompilerCausalQ16Coordinates parameters router tape ∈
      dependentSuccessfulSubtypeEvent q16DigestForestSucceeds
        (fun _residual =>
          successfulQ16DigestForestEquiv ⁻¹'
            q16SuccessfulCoordinatesBadEvent bad) := by
  let succeeds :=
    operational_realization_implies_q16_digest_forest_succeeds realized
  refine ⟨succeeds, ?_⟩
  exact operational_all_in_bad_implies_successful_coordinate_bad realized
    bad allBad

/-- Hidden-tape averaged q16 bound for any literal scheduler router.  The bad
set may depend on the hidden adversary tape and every non-q16 oracle answer.
The `covered` premise is intentionally the sole protocol-specific gap: it
must identify the accepted Tag-73 selected schedule with the forest routed
online by the scheduler. -/
theorem exact_compiler_causal_q16_event_probability_le_semantic
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (router : HiddenTape → ExactCompilerCausalQ16Router parameters)
    (bad : HiddenTape → ExactCompilerQ16Residual parameters →
      Finset (Fin 262144))
    (badCard : ∀ hidden residual, (bad hidden residual).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      exactCompilerCausalQ16Coordinates parameters (router hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent q16DigestForestSucceeds
          (fun residual => successfulQ16DigestForestEquiv ⁻¹'
            q16SuccessfulCoordinatesBadEvent (bad hidden residual))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      (Nat.choose 9557 16 : ENNReal) /
        (AspisK1.V7Tag73Q16CompactScheduleCount.semanticCompactFavourable :
          ENNReal) := by
  exact
    AspisK1.V7Tag73Q16SuccessfulForestBridge.exact_compiler_dependent_q16_event_probability_le
        hiddenLaw (exactCompilerTargetCaps parameters).length
        (fun hidden =>
          exactCompilerCausalQ16Coordinates parameters (router hidden))
        bad badCard reference traceExists event covered

#print axioms exactCompilerCausalQ16Coordinates
#print axioms operational_realization_covers_dependent_bad_coordinate
#print axioms exact_compiler_causal_q16_event_probability_le_semantic

end

end AspisK1.V7Tag73CausalQ16ProbabilityBridge
