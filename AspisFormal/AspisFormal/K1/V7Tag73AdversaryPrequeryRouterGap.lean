import AspisFormal.K1.V7Tag73FirstExposureRoleClassification
import AspisFormal.K1.V7Tag73K15SemanticSequentialRouter
import AspisFormal.K1.V7Tag73K15RelationAlphaPreAnswerRouters
import AspisFormal.K1.V7Tag73SchedulerHistoryQ16Router

/-!
# Exact adversary-prequery boundary of the current causal routers

The semantic, relation-alpha, and q16 coordinate routers correctly label a
missing verifier request from its pre-answer verifier history.  An earlier
fresh request by the arbitrary adversary is intentionally not given one of
those verifier slots.  If the verifier later requests the same input, the
lazy oracle returns a cache hit and the unified fresh-exposure router gets no
second coordinate to label.

This file records that boundary directly at `seekUnifiedExposure`.  Together
with the executable adversary-first/cache-hit witness, it rules out using any
of the three existing verifier-origin coordinate equivalences as an
unconditional source adapter.  It does not add a probability event, provider,
or protocol assumption.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73AdversaryPrequeryRouterGap

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73FirstExposureRoleClassification
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73K15SemanticSequentialRouter
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73SchedulerHistoryQ16Router
open AspisK1.V7Tag73TranscriptSchedule

/-! ## Verifier-only labels reject an adversary fresh exposure -/

theorem scheduler_semantic_label_of_adversary_fresh_is_none
    {globalOracleCalls : Nat} {MachineResult : Type}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (state : OracleState) (input : ShaInput)
    (nextProgram : ShaOutput → OracleMachine MachineResult)
    (remainingFuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (totalRoom : state.totalCalls < limits.totalCalls)
    (freshRoom : state.freshCalls < limits.freshCalls)
    (missing : lookupEntry state input = none)
    (onReturned : MachineResult → OracleState →
      UnifiedExposureCursor globalOracleCalls)
    (request : seekUnifiedExposure transitionFuel cursor =
      .machineFresh limits limitBound .adversary state input nextProgram
        remainingFuel coherent totalRoom freshRoom missing onReturned) :
    schedulerSemanticSequentialLabel transitionFuel cursor = none := by
  simp [schedulerSemanticSequentialLabel, request]

theorem scheduler_relation_alpha_label_of_adversary_fresh_is_none
    {globalOracleCalls : Nat} {MachineResult : Type}
    (round : Fin 4) (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (state : OracleState) (input : ShaInput)
    (nextProgram : ShaOutput → OracleMachine MachineResult)
    (remainingFuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (totalRoom : state.totalCalls < limits.totalCalls)
    (freshRoom : state.freshCalls < limits.freshCalls)
    (missing : lookupEntry state input = none)
    (onReturned : MachineResult → OracleState →
      UnifiedExposureCursor globalOracleCalls)
    (request : seekUnifiedExposure transitionFuel cursor =
      .machineFresh limits limitBound .adversary state input nextProgram
        remainingFuel coherent totalRoom freshRoom missing onReturned) :
    schedulerRelationAlphaLabel round transitionFuel cursor = none := by
  simp [schedulerRelationAlphaLabel, request]

theorem scheduler_q16_label_of_adversary_fresh_is_none
    {globalOracleCalls : Nat} {MachineResult : Type}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (state : OracleState) (input : ShaInput)
    (nextProgram : ShaOutput → OracleMachine MachineResult)
    (remainingFuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (totalRoom : state.totalCalls < limits.totalCalls)
    (freshRoom : state.freshCalls < limits.freshCalls)
    (missing : lookupEntry state input = none)
    (onReturned : MachineResult → OracleState →
      UnifiedExposureCursor globalOracleCalls)
    (request : seekUnifiedExposure transitionFuel cursor =
      .machineFresh limits limitBound .adversary state input nextProgram
        remainingFuel coherent totalRoom freshRoom missing onReturned) :
    schedulerHistoryQ16Label transitionFuel cursor = none := by
  simp [schedulerHistoryQ16Label, request]

/-- One literal adversary fresh exposure is ignored by every existing
verifier-origin K1.3/K1.5 router, even when its bytes have the deployed
squeeze shape.  This is the exact model boundary; it is not repaired by
changing the later verifier label. -/
theorem existing_verifier_origin_routers_do_not_label_adversary_first_exposure
    {globalOracleCalls : Nat} {MachineResult : Type}
    (round : Fin 4) (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (state : OracleState) (digest : Digest256)
    (nextProgram : ShaOutput → OracleMachine MachineResult)
    (remainingFuel : Nat)
    (coherent : HistoryTotalCoherent state)
    (totalRoom : state.totalCalls < limits.totalCalls)
    (freshRoom : state.freshCalls < limits.freshCalls)
    (missing : lookupEntry state (bytes digest ++ [domSqueeze]) = none)
    (onReturned : MachineResult → OracleState →
      UnifiedExposureCursor globalOracleCalls)
    (request : seekUnifiedExposure transitionFuel cursor =
      .machineFresh limits limitBound .adversary state
        (bytes digest ++ [domSqueeze]) nextProgram remainingFuel coherent
          totalRoom freshRoom missing onReturned) :
    schedulerSemanticSequentialLabel transitionFuel cursor = none ∧
      schedulerRelationAlphaLabel round transitionFuel cursor = none ∧
      schedulerHistoryQ16Label transitionFuel cursor = none := by
  exact ⟨
    scheduler_semantic_label_of_adversary_fresh_is_none transitionFuel cursor
      limits limitBound state (bytes digest ++ [domSqueeze]) nextProgram
      remainingFuel coherent totalRoom freshRoom missing onReturned request,
    scheduler_relation_alpha_label_of_adversary_fresh_is_none round
      transitionFuel cursor limits limitBound state
      (bytes digest ++ [domSqueeze]) nextProgram remainingFuel coherent
      totalRoom freshRoom missing onReturned request,
    scheduler_q16_label_of_adversary_fresh_is_none transitionFuel cursor limits
      limitBound state (bytes digest ++ [domSqueeze]) nextProgram
      remainingFuel coherent totalRoom freshRoom missing onReturned request⟩

/-! ## The later operational use is a cache hit, not a new routed answer -/

/-- The executable witness from the classification audit has exactly one
fresh answer: the adversary creates it and the verifier reuses it from cache.
Thus a fresh-exposure coordinate router has no later coordinate on which it
could repair the missing verifier-role label. -/
theorem adversary_first_then_verifier_cached_has_one_fresh_answer
    (before answer : Digest256) :
    (adversaryFirstSqueezeState before answer).freshCalls = 1 ∧
      (verifierCachedSqueezeState before answer).freshCalls = 1 ∧
      (verifierCachedSqueezeState before answer).history =
        (adversaryFirstSqueezeState before answer).history ++
          [{ input := bytes before ++ [domSqueeze]
             output := answer
             actor := .verifier
             origin := .cached }] := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms scheduler_semantic_label_of_adversary_fresh_is_none
#print axioms scheduler_relation_alpha_label_of_adversary_fresh_is_none
#print axioms scheduler_q16_label_of_adversary_fresh_is_none
#print axioms
  existing_verifier_origin_routers_do_not_label_adversary_first_exposure
#print axioms adversary_first_then_verifier_cached_has_one_fresh_answer

end AspisK1.V7Tag73AdversaryPrequeryRouterGap
