import AspisFormal.K1.V7Tag73PersistentTranscriptRoles
import AspisFormal.K1.V7Tag73ExactFixedFullRunFactorization

/-!
# Persistent-role cache erasure

This file gives the persistent pre-answer role automaton a source-neutral
semantic cache view.  A cache entry consists only of an existing operational
table entry together with the role already bound to its input.  Consequently
erasing tags is definitionally the current oracle table, and a cache hit cannot
acquire a role from its answer or from completed future context.

The same construction tags the canonical fixed-root exposure records and
erases definitionally to `exactFixedRootRecords`.  This last theorem is a
conservativity theorem, not a source-binding theorem: connecting the tags to a
Rust control-state label still requires the current-revision source projection
to expose that label before the answer is consumed.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73PersistentRoleCacheErasure

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73VerifierOracleStability
open AspisK1.V7Tag73PersistentTranscriptRoles
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalRootPackage

noncomputable section

universe u

/-! ## A tagged view of the operational lazy-oracle cache -/

/-- One operational table entry with the role fixed for its input, if any. -/
structure PersistentRoleCacheEntry (Role : Type u) where
  operational : TableEntry
  role? : Option Role

/-- Tag every existing table entry using only the persistent input map. -/
def persistentRoleCache
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (oracle : OracleState) : List (PersistentRoleCacheEntry Role) :=
  oracle.table.map fun entry =>
    { operational := entry
      role? := roles.roleForInput? entry.input }

/-- Erase the ghost tag from a semantic cache entry. -/
def PersistentRoleCacheEntry.erase
    {Role : Type u} (entry : PersistentRoleCacheEntry Role) : TableEntry :=
  entry.operational

/-- The tagged cache is observationally exactly the production oracle table. -/
@[simp] theorem persistent_role_cache_erases
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (oracle : OracleState) :
    (persistentRoleCache roles oracle).map PersistentRoleCacheEntry.erase =
      oracle.table := by
  unfold persistentRoleCache
  rw [List.map_map]
  change oracle.table.map (fun entry => entry) = oracle.table
  simp

/-- Exact cache lookup.  The operational lookup chooses the entry; the ghost
role lookup merely reads the binding that existed before the cache hit. -/
def lookupPersistentRoleCache
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (oracle : OracleState) (input : ShaInput) :
    Option (PersistentRoleCacheEntry Role) :=
  (lookupEntry oracle input).map fun entry =>
    { operational := entry
      role? := roles.roleForInput? input }

/-- Erasing a tagged lookup is exactly the production table lookup. -/
@[simp] theorem lookup_persistent_role_cache_erases
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (oracle : OracleState) (input : ShaInput) :
    (lookupPersistentRoleCache roles oracle input).map
        PersistentRoleCacheEntry.erase = lookupEntry oracle input := by
  unfold lookupPersistentRoleCache
  cases lookupEntry oracle input <;> rfl

theorem lookup_persistent_role_cache_inherits_bound_role
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (oracle : OracleState) (input : ShaInput) (entry : TableEntry)
    (role : Role) (found : lookupEntry oracle input = some entry)
    (bound : roles.roleForInput? input = some role) :
    lookupPersistentRoleCache roles oracle input =
      some { operational := entry, role? := some role } := by
  simp [lookupPersistentRoleCache, found, bound]

/-! ## Cache hits preserve the original tag -/

/-- A successful query of an already-defined coordinate changes neither the
operational table nor the persistent role map.  Hence its complete tagged
cache is literally unchanged. -/
theorem successful_cached_query_preserves_persistent_role_cache
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor)
    (state nextState : PersistentRoleMachineState Control Role)
    (input : ShaInput) (entry : TableEntry) (output : ShaOutput)
    (observation : Option (PersistentRoleObservation Role))
    (found : lookupEntry state.oracle input = some entry)
    (success : queryOracleWithExecutableRoles policy controller limits actor
      state input = .ok (output, nextState, observation)) :
    persistentRoleCache nextState.roles nextState.oracle =
      persistentRoleCache state.roles state.oracle := by
  have roleExact : nextState.roles = state.roles := by
    rw [successful_executable_query_threads_preanswer_roles policy controller
      limits actor state nextState input output observation success]
    exact prepare_executable_existing_input_preserves_roles policy actor state
      input entry found
  have erased := query_oracle_with_executable_roles_erases policy controller
    limits actor state input
  rw [success] at erased
  change Except.ok (output, nextState.oracle) =
    queryOracle controller limits actor state.oracle input at erased
  have operationalSuccess :
      queryOracle controller limits actor state.oracle input =
        .ok (output, nextState.oracle) := by
    exact erased.symm
  obtain ⟨record, _history, _recordInput, _recordOutput, _recordActor,
      fresh | cached⟩ :=
    query_oracle_success_table_history_cases controller limits actor
      state.oracle nextState.oracle input output operationalSuccess
  · have missing := fresh.2.2
    rw [found] at missing
    contradiction
  · simp [persistentRoleCache, roleExact, cached.2]

/-- Any role observation returned on a cache hit is exactly the tag that was
already installed before the hit.  Its source is the source of the original
table installation. -/
theorem successful_cached_query_inherits_original_role_and_source
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor)
    (state nextState : PersistentRoleMachineState Control Role)
    (input : ShaInput) (entry : TableEntry) (output : ShaOutput)
    (observation : PersistentRoleObservation Role)
    (found : lookupEntry state.oracle input = some entry)
    (success : queryOracleWithExecutableRoles policy controller limits actor
      state input = .ok (output, nextState, some observation)) :
    state.roles.roleForInput? input = some observation.role ∧
      observation.input = input ∧
      observation.output = entry.output ∧
      observation.use = .cached entry.source := by
  have preparedRoles :
      (prepareExecutableRoleInput policy actor state input).roles =
        state.roles :=
    prepare_executable_existing_input_preserves_roles policy actor state input
      entry found
  unfold queryOracleWithExecutableRoles at success
  simp only [prepare_executable_role_input_oracle] at success
  by_cases blocked : state.oracle.totalCalls ≥ limits.totalCalls
  · simp [queryOracle, blocked] at success
  · simp [queryOracle, blocked, found] at success
    rcases success with ⟨rfl, rfl, observationExact⟩
    rw [preparedRoles] at observationExact
    unfold queryRoleObservation? at observationExact
    cases selected : state.roles.roleForInput? input with
    | none => simp [selected] at observationExact
    | some installedRole =>
        simp only [selected, found, Option.map_some, Option.some.injEq]
          at observationExact
        have exactObservation : observation =
            { role := installedRole
              input := input
              output := entry.output
              use := .cached entry.source } := observationExact.symm
        subst observation
        exact ⟨by simpa using selected, rfl, rfl, rfl⟩

/-- Direct cache formulation of the inheritance result: the observation on a
hit reads the already-present tagged entry and its original source. -/
theorem successful_cached_query_reads_original_tagged_entry
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor)
    (state nextState : PersistentRoleMachineState Control Role)
    (input : ShaInput) (entry : TableEntry) (output : ShaOutput)
    (observation : PersistentRoleObservation Role)
    (found : lookupEntry state.oracle input = some entry)
    (success : queryOracleWithExecutableRoles policy controller limits actor
      state input = .ok (output, nextState, some observation)) :
    lookupPersistentRoleCache state.roles state.oracle input =
        some { operational := entry, role? := some observation.role } ∧
      observation.input = input ∧
      observation.output = entry.output ∧
      observation.use = .cached entry.source := by
  obtain ⟨bound, inputExact, outputExact, sourceExact⟩ :=
    successful_cached_query_inherits_original_role_and_source policy controller
      limits actor state nextState input entry output observation found success
  exact ⟨lookup_persistent_role_cache_inherits_bound_role state.roles
    state.oracle input entry observation.role found bound,
    inputExact, outputExact, sourceExact⟩

/-! ## First fresh and programmed installations -/

/-- A successful missing-input query appends exactly one tagged fresh entry.
The role in the new cache entry is the one installed by the pre-answer
preparation, so it cannot depend on the sampled output. -/
theorem successful_fresh_query_appends_preanswer_tagged_entry
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor)
    (state nextState : PersistentRoleMachineState Control Role)
    (input : ShaInput) (output : ShaOutput)
    (observation : Option (PersistentRoleObservation Role))
    (role : Role)
    (missing : lookupEntry state.oracle input = none)
    (prebound :
      (prepareExecutableRoleInput policy actor state input).roles.roleForInput?
        input = some role)
    (success : queryOracleWithExecutableRoles policy controller limits actor
      state input = .ok (output, nextState, observation)) :
    persistentRoleCache nextState.roles nextState.oracle =
      persistentRoleCache
          (prepareExecutableRoleInput policy actor state input).roles
          state.oracle ++
        [{ operational :=
            { input := input, output := output, source := .fresh }
           role? := some role }] := by
  have rolesExact := successful_executable_query_threads_preanswer_roles policy
    controller limits actor state nextState input output observation success
  have erased := query_oracle_with_executable_roles_erases policy controller
    limits actor state input
  rw [success] at erased
  change Except.ok (output, nextState.oracle) =
    queryOracle controller limits actor state.oracle input at erased
  have operationalSuccess :
      queryOracle controller limits actor state.oracle input =
        .ok (output, nextState.oracle) := by
    exact erased.symm
  have tableExact : nextState.oracle.table = state.oracle.table ++
      [{ input := input, output := output, source := .fresh }] := by
    unfold queryOracle at operationalSuccess
    split at operationalSuccess <;> try contradiction
    next _ =>
      split at operationalSuccess
      next entry found =>
        rw [missing] at found
        contradiction
      next _ =>
        split at operationalSuccess <;> try contradiction
        next _ =>
          split at operationalSuccess
          next _ => contradiction
          next answer answered =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at operationalSuccess
            rcases operationalSuccess with ⟨rfl, stateExact⟩
            exact (congrArg OracleState.table stateExact).symm
  rw [rolesExact]
  unfold persistentRoleCache
  rw [tableExact, List.map_append]
  simp [prebound]

/-- Successful programming appends one tagged programmed entry with the role
chosen before `programOracle` is executed. -/
theorem successful_program_appends_preanswer_tagged_entry
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (limits : OracleLimits) (actor : QueryActor)
    (state nextState : PersistentRoleMachineState Control Role)
    (programming : Programming)
    (observation : Option (PersistentRoleObservation Role))
    (role : Role)
    (prebound :
      (prepareExecutableRoleInput policy actor state
        programming.input).roles.roleForInput? programming.input = some role)
    (success : programOracleWithExecutableRoles policy limits actor state
      programming = .ok (nextState, observation)) :
    persistentRoleCache nextState.roles nextState.oracle =
      persistentRoleCache
          (prepareExecutableRoleInput policy actor state
            programming.input).roles state.oracle ++
        [{ operational :=
            { input := programming.input
              output := programming.output
              source := .programmed }
           role? := some role }] := by
  have rolesExact := successful_executable_program_threads_preanswer_roles
    policy limits actor state nextState programming observation success
  have erased := program_oracle_with_executable_roles_erases policy limits actor
    state programming
  rw [success] at erased
  change Except.ok nextState.oracle =
    programOracle limits actor state.oracle programming at erased
  have operationalSuccess :
      programOracle limits actor state.oracle programming =
        .ok nextState.oracle := by
    exact erased.symm
  have exact := AspisK1.V7Tag73AtomicPairReplay.program_oracle_success_exact
    limits actor state.oracle nextState.oracle programming operationalSuccess
  rw [rolesExact]
  unfold persistentRoleCache
  rw [exact.2.2.1, List.map_append]
  simp [prebound]

/-! ## Exact erasure of canonical fixed-root records -/

/-- The input whose answer is sampled by a unified exposure record, when the
record represents an oracle coordinate rather than padding. -/
def UnifiedExposureRecord.roleInput? : UnifiedExposureRecord → Option ShaInput
  | .padding _ => none
  | .machineFresh _ input _ => some input
  | .forkOutput _ outputInput _ _ _ => some outputInput
  | .forkAdvance scheduled => some scheduled.advanceInput

/-- A ghost-tagged exposure record. -/
structure PersistentRoleExposureRecord (Role : Type u) where
  operational : UnifiedExposureRecord
  role? : Option Role

def tagExposureRecord
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (record : UnifiedExposureRecord) : PersistentRoleExposureRecord Role :=
  { operational := record
    role? := (UnifiedExposureRecord.roleInput? record).bind
      roles.roleForInput? }

def tagExposureRecords
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (records : List UnifiedExposureRecord) :
    List (PersistentRoleExposureRecord Role) :=
  records.map (tagExposureRecord roles)

@[simp] theorem tag_exposure_records_erase
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (records : List UnifiedExposureRecord) :
    (tagExposureRecords roles records).map
        PersistentRoleExposureRecord.operational = records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      simp only [tagExposureRecords, List.map_cons]
      exact congrArg (List.cons record) ih

/-- Canonical root records equipped with the same persistent role map. -/
def taggedExactFixedRootRecords
    {Role HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration
      HiddenTape TapeIdentity Observation Statement Proof Payload Result
        parameters}
    {projection : AcceptedTapeProjection
      Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape
      parameters}
    (roles : PersistentTranscriptRoles Role)
    (package : ExactFixedCleanCompletedRootPackage
      transitionFuel configuration projection fixedInstance sample) :
    List (PersistentRoleExposureRecord Role) :=
  tagExposureRecords roles (exactFixedRootRecords package)

/-- Erasing all ghost tags gives the literal existing `exactFixedRootRecords`;
no production trace, byte, challenge, cache, or scheduler definition changes. -/
@[simp] theorem tagged_exact_fixed_root_records_erase
    {Role HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration
      HiddenTape TapeIdentity Observation Statement Proof Payload Result
        parameters}
    {projection : AcceptedTapeProjection
      Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape
      parameters}
    (roles : PersistentTranscriptRoles Role)
    (package : ExactFixedCleanCompletedRootPackage
      transitionFuel configuration projection fixedInstance sample) :
    (taggedExactFixedRootRecords roles package).map
        PersistentRoleExposureRecord.operational =
      exactFixedRootRecords package := by
  simp [taggedExactFixedRootRecords]

#print axioms persistent_role_cache_erases
#print axioms lookup_persistent_role_cache_erases
#print axioms lookup_persistent_role_cache_inherits_bound_role
#print axioms successful_cached_query_preserves_persistent_role_cache
#print axioms successful_cached_query_inherits_original_role_and_source
#print axioms successful_cached_query_reads_original_tagged_entry
#print axioms successful_fresh_query_appends_preanswer_tagged_entry
#print axioms successful_program_appends_preanswer_tagged_entry
#print axioms tag_exposure_records_erase
#print axioms tagged_exact_fixed_root_records_erase

end

end AspisK1.V7Tag73PersistentRoleCacheErasure
