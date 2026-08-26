import AspisFormal.K1.V7Tag73SchedulerMachineFactorization
import AspisFormal.K1.V7Tag73TotalizedMachineReflection

/-!
# Finite completion of a guarded totalized oracle stage

The native scheduler pauses immediately before every missing lazy-oracle
query.  This leaf proves directly that a totalized `OracleMachine` guarded by
`StageHasOracleRoom` cannot pause in an abort/resource/fuel state and consumes
at most its machine fuel many supplied fresh answers before returning.

The proof is independent of the Tag-73 dispatcher.  It exists as a small leaf
so the large operational-completion theorem only composes already checked
machine and fork facts.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73TotalizedStageCompletion

set_option maxRecDepth 8192

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73ConcreteRestorationClient

noncomputable section

universe u v

/-- Exact normal forms of the normalizer applied to a mapped totalization.
The request constructor retains the literal residual original program, strict
fuel decrease, and the room invariant before the pending query. -/
inductive MappedTotalizedSeekCertificate
    {Original : Type u} {Mapped : Type v}
    (limits : OracleLimits) (actor : QueryActor)
    (map : Except TotalizedMachineFailure Original → Mapped) :
    (fuel : Nat) → (state : OracleState) →
      (program : OracleMachine Original) →
      (coherent : HistoryTotalCoherent state) →
      SeekNextFreshResult Mapped limits → Prop where
  | returned
      (fuel : Nat) (state : OracleState) (program : OracleMachine Original)
      (coherent : HistoryTotalCoherent state)
      (value : Except TotalizedMachineFailure Original)
      (finalState : OracleState) (steps : Nat) :
      MappedTotalizedSeekCertificate limits actor map fuel state program
        coherent (.returned (map value) finalState steps)
  | request
      (fuel : Nat) (state : OracleState) (program : OracleMachine Original)
      (coherent : HistoryTotalCoherent state)
      (requestState : OracleState) (input : ShaInput)
      (nextOriginal : ShaOutput → OracleMachine Original)
      (remainingFuel steps : Nat)
      (requestCoherent : HistoryTotalCoherent requestState)
      (totalRoom : requestState.totalCalls < limits.totalCalls)
      (freshRoom : requestState.freshCalls < limits.freshCalls)
      (missing : lookupEntry requestState input = none)
      (remainingLt : remainingFuel < fuel)
      (stageRoom : StageHasOracleRoom limits requestState (remainingFuel + 1)) :
      MappedTotalizedSeekCertificate limits actor map fuel state program coherent
        (.request requestState input
          (fun answer => mapOracleMachineResult map
            (totalizeOracleMachine remainingFuel (nextOriginal answer)))
          remainingFuel steps requestCoherent totalRoom freshRoom missing)

/-- Executing a cached query preserves the exact normal form while adding one
completed call to its step counter. -/
theorem mapped_totalized_seek_certificate_add_completed
    {Original : Type u} {Mapped : Type v}
    (limits : OracleLimits) (actor : QueryActor)
    (map : Except TotalizedMachineFailure Original → Mapped)
    (outerFuel : Nat) (outerState : OracleState)
    (outerProgram : OracleMachine Original)
    (outerCoherent : HistoryTotalCoherent outerState)
    (innerFuel : Nat) (innerState : OracleState)
    (innerProgram : OracleMachine Original)
    (innerCoherent : HistoryTotalCoherent innerState)
    (result : SeekNextFreshResult Mapped limits)
    (innerLt : innerFuel < outerFuel)
    (certificate : MappedTotalizedSeekCertificate limits actor map innerFuel
      innerState innerProgram innerCoherent result) :
    MappedTotalizedSeekCertificate limits actor map outerFuel outerState
      outerProgram outerCoherent result.addCompletedQuery := by
  cases certificate with
  | returned value finalState steps =>
      exact .returned outerFuel outerState outerProgram outerCoherent value
        finalState (steps + 1)
  | request requestState input nextOriginal remainingFuel steps
      requestCoherent totalRoom freshRoom missing remainingLt stageRoom =>
      exact .request outerFuel outerState outerProgram outerCoherent requestState
        input nextOriginal remainingFuel (steps + 1) requestCoherent totalRoom
        freshRoom missing (remainingLt.trans innerLt) stageRoom

/-- The mapped totalization is either an ordinary mapped return or a live
fresh request whose continuation is the mapped residual totalization. -/
theorem seek_next_fresh_mapped_totalized_certificate
    {Original : Type u} {Mapped : Type v}
    (limits : OracleLimits) (actor : QueryActor)
    (map : Except TotalizedMachineFailure Original → Mapped) :
    ∀ (fuel : Nat) (state : OracleState)
      (program : OracleMachine Original)
      (coherent : HistoryTotalCoherent state),
      StageHasOracleRoom limits state fuel →
      MappedTotalizedSeekCertificate limits actor map fuel state program coherent
        (seekNextFresh limits actor fuel state
          (mapOracleMachineResult map (totalizeOracleMachine fuel program))
          coherent) := by
  intro fuel
  induction fuel with
  | zero =>
      intro state program coherent room
      cases program with
      | pure value =>
          exact .returned 0 state (.pure value) coherent (.ok value) state 0
      | abort reason =>
          exact .returned 0 state (.abort reason) coherent
            (.error (.oracleAbort reason)) state 0
      | query input next =>
          exact .returned 0 state (.query input next) coherent
            (.error .timeout) state 0
  | succ fuel ih =>
      intro state program coherent room
      cases program with
      | pure value =>
          exact .returned (fuel + 1) state (.pure value) coherent (.ok value)
            state 0
      | abort reason =>
          exact .returned (fuel + 1) state (.abort reason) coherent
            (.error (.oracleAbort reason)) state 0
      | query input next =>
          simp only [totalizeOracleMachine, mapOracleMachineResult,
            seekNextFresh]
          split
          next totalBlocked =>
            unfold StageHasOracleRoom at room
            omega
          next totalRoom =>
            split
            next entry found =>
              have cachedRoom : StageHasOracleRoom limits
                  (cachedQueryState actor state input entry) fuel := by
                unfold StageHasOracleRoom at room ⊢
                simp [cachedQueryState]
                omega
              have tail := ih (cachedQueryState actor state input entry)
                (next entry.output)
                (cached_query_state_preserves_history_total_coherent actor state
                  input entry coherent) cachedRoom
              exact mapped_totalized_seek_certificate_add_completed limits actor
                map (fuel + 1) state (.query input next) coherent fuel
                (cachedQueryState actor state input entry) (next entry.output)
                (cached_query_state_preserves_history_total_coherent actor state
                  input entry coherent) _ (by omega) tail
            next missing =>
              split
              next freshBlocked =>
                unfold StageHasOracleRoom at room
                omega
              next freshRoom =>
                exact .request (fuel + 1) state (.query input next) coherent
                  state input next fuel 0 coherent
                  (Nat.lt_of_not_ge totalRoom)
                  (Nat.lt_of_not_ge freshRoom) missing (by omega) room

/-- Supplying at least `fuel` coordinates to a guarded totalized stage always
produces a projected normal return.  Cached calls reduce the actual number of
consumed coordinates. -/
theorem consume_mapped_totalized_stage_returns
    {Original : Type u} {Mapped : Type v}
    (limits : OracleLimits) (actor : QueryActor)
    (map : Except TotalizedMachineFailure Original → Mapped) :
    ∀ (fuel : Nat) (available : List Digest256) (state : OracleState)
      (program : OracleMachine Original)
      (coherent : HistoryTotalCoherent state),
      StageHasOracleRoom limits state fuel →
      fuel ≤ available.length →
      ∃ returned : ProjectedMachinePrefixReturned limits actor fuel state
          (mapOracleMachineResult map (totalizeOracleMachine fuel program))
          available,
        consumeProjectedMachinePrefix limits actor available fuel state
            (mapOracleMachineResult map (totalizeOracleMachine fuel program))
            coherent = .ok returned := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro available state program coherent room enough
      have certificate := seek_next_fresh_mapped_totalized_certificate limits
        actor map fuel state program coherent room
      unfold consumeProjectedMachinePrefix
      unfold certifiedSeekNextFresh
      unfold consumeCertifiedProjectedMachinePrefix
      split
      next result finalState steps sought =>
        exact ⟨_, rfl⟩
      next reason finalState steps sought =>
        have impossible := certificate
        have soughtValue : seekNextFresh limits actor fuel state
            (mapOracleMachineResult map
              (totalizeOracleMachine fuel program)) coherent =
              .explicitAbort reason finalState steps := by
          simpa only using sought
        rw [soughtValue] at impossible
        cases impossible
      next reason finalState steps sought =>
        have impossible := certificate
        have soughtValue : seekNextFresh limits actor fuel state
            (mapOracleMachineResult map
              (totalizeOracleMachine fuel program)) coherent =
              .resourceAbort reason finalState steps := by
          simpa only using sought
        rw [soughtValue] at impossible
        cases impossible
      next finalState steps sought =>
        have impossible := certificate
        have soughtValue : seekNextFresh limits actor fuel state
            (mapOracleMachineResult map
              (totalizeOracleMachine fuel program)) coherent =
              .outOfFuel finalState steps := by
          simpa only using sought
        rw [soughtValue] at impossible
        cases impossible
      next requestState input nextMapped remainingFuel steps requestCoherent
          totalRoom freshRoom missing sought =>
        have aligned := certificate
        have soughtValue : seekNextFresh limits actor fuel state
            (mapOracleMachineResult map
              (totalizeOracleMachine fuel program)) coherent =
              .request requestState input nextMapped remainingFuel steps
                requestCoherent totalRoom freshRoom missing := by
          simpa only using sought
        rw [soughtValue] at aligned
        cases aligned with
        | request _ _ nextOriginal _ _ _ _ _ _ remainingLt requestRoom =>
          cases available with
          | nil =>
              simp only [List.length_nil] at enough
              omega
          | cons answer rest =>
              have afterRoom : StageHasOracleRoom limits
                  (freshQueryState actor requestState input answer)
                  remainingFuel := by
                unfold StageHasOracleRoom at requestRoom ⊢
                simp [freshQueryState]
                omega
              have restEnough : remainingFuel ≤ rest.length := by
                simp only [List.length_cons] at enough
                omega
              obtain ⟨tail, tailExact⟩ := ih remainingFuel remainingLt rest
                (freshQueryState actor requestState input answer)
                (nextOriginal answer)
                (fresh_query_state_preserves_history_total_coherent actor
                  requestState input answer requestCoherent) afterRoom restEnough
              unfold consumeProjectedMachinePrefix at tailExact
              dsimp only
              rw [tailExact]
              exact ⟨_, rfl⟩

#print axioms seek_next_fresh_mapped_totalized_certificate
#print axioms consume_mapped_totalized_stage_returns

end

end AspisK1.V7Tag73TotalizedStageCompletion
