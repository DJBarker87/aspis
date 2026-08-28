import AspisFormal.K1.V7Tag73AtomicPairReplay
import AspisFormal.K1.V7Tag73VerifierOracleStability

/-!
# Persistent causal roles for transcript oracle inputs

This file provides a small instrumentation layer for assigning semantic roles
to exact SHA inputs before those inputs are answered.  A role assignment is
persistent: unrelated oracle calls do not reset it, and a later cached reuse
is classified by the source tag of the table entry installed at the first
fresh query or programming operation.

The instrumentation executes the existing `queryOracle` and `programOracle`
definitions verbatim.  Its erasure theorems therefore expose no replacement
oracle semantics and make no probability claim.  In particular, the layer
does not guess a role from a completed transcript: callers must install the
exact expected input when it becomes available from already-observed state.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73PersistentTranscriptRoles

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73VerifierOracleStability

noncomputable section

universe u

/-- One role fixed together with its exact expected SHA input. -/
structure PersistentTranscriptRole (Role : Type u) where
  role : Role
  input : ShaInput

/-- Ordered persistent role bindings.  The first binding for an input wins,
matching the first-entry lookup convention of the operational oracle table. -/
structure PersistentTranscriptRoles (Role : Type u) where
  bindings : List (PersistentTranscriptRole Role)

def PersistentTranscriptRoles.empty {Role : Type u} :
    PersistentTranscriptRoles Role :=
  { bindings := [] }

/-- Internal append used only after the public guarded pre-answer check. -/
private def PersistentTranscriptRoles.appendBinding {Role : Type u}
    (roles : PersistentTranscriptRoles Role) (role : Role)
    (input : ShaInput) : PersistentTranscriptRoles Role :=
  { bindings := roles.bindings ++ [{ role := role, input := input }] }

/-- Deterministically recover the first pre-installed role for an input. -/
def PersistentTranscriptRoles.roleForInput?
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (input : ShaInput) : Option Role :=
  (roles.bindings.find? fun binding => binding.input = input).map
    PersistentTranscriptRole.role

/-- The first input already assigned to a role. -/
def PersistentTranscriptRoles.inputForRole?
    {Role : Type u} [DecidableEq Role]
    (roles : PersistentTranscriptRoles Role) (role : Role) : Option ShaInput :=
  (roles.bindings.find? fun binding => binding.role = role).map
    PersistentTranscriptRole.input

/-- A role can be installed only before the input has any oracle-table entry,
and only while both the role and input are unbound.  Returning `none` is an
executable refusal, not an asserted causal premise. -/
def PersistentTranscriptRoles.guardedInstall
    {Role : Type u} [DecidableEq Role]
    (roles : PersistentTranscriptRoles Role) (state : OracleState)
    (role : Role) (input : ShaInput) :
    Option (PersistentTranscriptRoles Role) :=
  if roles.inputForRole? role |>.isSome then none
  else if roles.roleForInput? input |>.isSome then none
  else if lookupEntry state input |>.isSome then none
  else some (roles.appendBinding role input)

@[simp] theorem empty_role_for_input
    {Role : Type u} (input : ShaInput) :
    ((PersistentTranscriptRoles.empty : PersistentTranscriptRoles Role)
        |>.roleForInput? input) = none := by
  rfl

private theorem role_for_input_append_self_of_unbound
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (role : Role) (input : ShaInput)
    (unbound : roles.roleForInput? input = none) :
    (roles.appendBinding role input).roleForInput? input = some role := by
  unfold PersistentTranscriptRoles.roleForInput? at unbound ⊢
  unfold PersistentTranscriptRoles.appendBinding
  have noBinding :
      roles.bindings.find? (fun binding => binding.input = input) = none := by
    cases found : roles.bindings.find?
        (fun binding => binding.input = input) with
    | none => simpa [found]
    | some binding => simp [found] at unbound
  simp [noBinding]

/-- Appending a binding for one exact input leaves every different input's
earlier role unchanged.  This is the basic unrelated-call persistence fact. -/
private theorem role_for_input_append_other
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (role : Role) (installedInput queriedInput : ShaInput)
    (different : installedInput ≠ queriedInput) :
    (roles.appendBinding role installedInput).roleForInput? queriedInput =
      roles.roleForInput? queriedInput := by
  unfold PersistentTranscriptRoles.roleForInput?
  unfold PersistentTranscriptRoles.appendBinding
  simp [different]

theorem guarded_install_rejects_existing_table_entry
    {Role : Type u} [DecidableEq Role]
    (roles : PersistentTranscriptRoles Role) (state : OracleState)
    (role : Role) (input : ShaInput) (entry : TableEntry)
    (found : lookupEntry state input = some entry) :
    roles.guardedInstall state role input = none := by
  simp [PersistentTranscriptRoles.guardedInstall, found]

theorem guarded_install_rejects_bound_role
    {Role : Type u} [DecidableEq Role]
    (roles : PersistentTranscriptRoles Role) (state : OracleState)
    (role : Role) (input existing : ShaInput)
    (bound : roles.inputForRole? role = some existing) :
    roles.guardedInstall state role input = none := by
  simp [PersistentTranscriptRoles.guardedInstall, bound]

theorem guarded_install_rejects_bound_input
    {Role : Type u} [DecidableEq Role]
    (roles : PersistentTranscriptRoles Role) (state : OracleState)
    (role existingRole : Role) (input : ShaInput)
    (bound : roles.roleForInput? input = some existingRole) :
    roles.guardedInstall state role input = none := by
  by_cases roleBound : roles.inputForRole? role |>.isSome
  · simp [PersistentTranscriptRoles.guardedInstall, roleBound]
  · simp [PersistentTranscriptRoles.guardedInstall, roleBound, bound]

theorem guarded_install_success_binds_exact_input
    {Role : Type u} [DecidableEq Role]
    (roles installed : PersistentTranscriptRoles Role) (state : OracleState)
    (role : Role) (input : ShaInput)
    (success : roles.guardedInstall state role input = some installed) :
    installed.roleForInput? input = some role ∧
      roles.roleForInput? input = none ∧
      roles.inputForRole? role = none ∧
      lookupEntry state input = none := by
  unfold PersistentTranscriptRoles.guardedInstall at success
  split at success <;> try contradiction
  next roleFree =>
    split at success <;> try contradiction
    next inputFree =>
      split at success <;> try contradiction
      next tableFree =>
        simp only [Option.some.injEq] at success
        subst installed
        have inputNone : roles.roleForInput? input = none := by
          cases selected : roles.roleForInput? input <;>
            simp [selected] at inputFree ⊢
        have roleNone : roles.inputForRole? role = none := by
          cases selected : roles.inputForRole? role <;>
            simp [selected] at roleFree ⊢
        have tableNone : lookupEntry state input = none := by
          cases selected : lookupEntry state input <;>
            simp [selected] at tableFree ⊢
        exact ⟨role_for_input_append_self_of_unbound roles role input inputNone,
          inputNone, roleNone, tableNone⟩

/-- How an operational call used a persistent role.  `cached source` retains
whether the first table installation was fresh or programmed. -/
inductive PersistentRoleUse where
  | fresh
  | programmed
  | cached (source : TableSource)
  deriving DecidableEq, Repr

structure PersistentRoleObservation (Role : Type u) where
  role : Role
  input : ShaInput
  output : ShaOutput
  use : PersistentRoleUse

/-- Pre-state classification of a successful query.  A missing input is the
first fresh exposure; an existing input is a cache hit whose source is read
from the already-existing table entry. -/
def queryRoleObservation? {Role : Type u}
    (roles : PersistentTranscriptRoles Role) (state : OracleState)
    (input : ShaInput) (output : ShaOutput) :
    Option (PersistentRoleObservation Role) :=
  roles.roleForInput? input |>.map fun role =>
    { role := role
      input := input
      output := output
      use := match lookupEntry state input with
        | none => .fresh
        | some entry => .cached entry.source }

/-- Programming is a first programmed exposure whenever it succeeds. -/
def programmingRoleObservation? {Role : Type u}
    (roles : PersistentTranscriptRoles Role) (programming : Programming) :
    Option (PersistentRoleObservation Role) :=
  roles.roleForInput? programming.input |>.map fun role =>
    { role := role
      input := programming.input
      output := programming.output
      use := .programmed }

/-- An executable role policy evaluated before the current answer exists. -/
abbrev PreAnswerRolePolicy (Role : Type u) :=
  PersistentTranscriptRoles Role → OracleState → ShaInput → Option Role

/-- Oracle state paired with the persistent role tracker. -/
structure PersistentRoleOracleState (Role : Type u) where
  oracle : OracleState
  roles : PersistentTranscriptRoles Role

/-- Apply a policy before answering the input.  The guarded installer makes
the policy ineffective on cached inputs and on already-bound roles/inputs. -/
def preparePersistentRoleInput
    {Role : Type u} [DecidableEq Role]
    (policy : PreAnswerRolePolicy Role)
    (state : PersistentRoleOracleState Role) (input : ShaInput) :
    PersistentRoleOracleState Role :=
  match policy state.roles state.oracle input with
  | none => state
  | some role =>
      match state.roles.guardedInstall state.oracle role input with
      | none => state
      | some roles => { oracle := state.oracle, roles := roles }

@[simp] theorem prepare_persistent_role_input_oracle
    {Role : Type u} [DecidableEq Role]
    (policy : PreAnswerRolePolicy Role)
    (state : PersistentRoleOracleState Role) (input : ShaInput) :
    (preparePersistentRoleInput policy state input).oracle = state.oracle := by
  unfold preparePersistentRoleInput
  split
  · rfl
  · split <;> rfl

/-- No policy can retrospectively assign a cached input. -/
theorem prepare_existing_input_preserves_roles
    {Role : Type u} [DecidableEq Role]
    (policy : PreAnswerRolePolicy Role)
    (state : PersistentRoleOracleState Role) (input : ShaInput)
    (entry : TableEntry) (found : lookupEntry state.oracle input = some entry) :
    (preparePersistentRoleInput policy state input).roles = state.roles := by
  unfold preparePersistentRoleInput
  split <;> try rfl
  next role policyExact =>
    rw [guarded_install_rejects_existing_table_entry state.roles state.oracle
      role input entry found]

/-- The policy and guarded installation are run before `queryOracle`; the
result carries the same tracker into the continuation. -/
def queryOracleWithPreAnswerRoles
    {Role : Type u} [DecidableEq Role]
    (policy : PreAnswerRolePolicy Role)
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state : PersistentRoleOracleState Role)
    (input : ShaInput) :
    Except OracleAbort
      (ShaOutput × PersistentRoleOracleState Role ×
        Option (PersistentRoleObservation Role)) :=
  let prepared := preparePersistentRoleInput policy state input
  match queryOracle controller limits actor prepared.oracle input with
  | .error reason => .error reason
  | .ok (output, nextOracle) =>
      .ok (output,
        { oracle := nextOracle, roles := prepared.roles },
        queryRoleObservation? prepared.roles prepared.oracle input output)

/-- Programming uses the same pre-answer guard and carries the tracker into
the continuation unchanged. -/
def programOracleWithPreAnswerRoles
    {Role : Type u} [DecidableEq Role]
    (policy : PreAnswerRolePolicy Role) (limits : OracleLimits)
    (actor : QueryActor) (state : PersistentRoleOracleState Role)
    (programming : Programming) :
    Except OracleAbort
      (PersistentRoleOracleState Role ×
        Option (PersistentRoleObservation Role)) :=
  let prepared := preparePersistentRoleInput policy state programming.input
  match programOracle limits actor prepared.oracle programming with
  | .error reason => .error reason
  | .ok nextOracle =>
      .ok ({ oracle := nextOracle, roles := prepared.roles },
        programmingRoleObservation? prepared.roles programming)

theorem query_oracle_with_preanswer_roles_erases
    {Role : Type u} [DecidableEq Role]
    (policy : PreAnswerRolePolicy Role)
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state : PersistentRoleOracleState Role)
    (input : ShaInput) :
    (queryOracleWithPreAnswerRoles policy controller limits actor state input).map
        (fun result => (result.1, result.2.1.oracle)) =
      queryOracle controller limits actor state.oracle input := by
  simp only [queryOracleWithPreAnswerRoles,
    prepare_persistent_role_input_oracle]
  cases queryOracle controller limits actor state.oracle input <;> rfl

theorem program_oracle_with_preanswer_roles_erases
    {Role : Type u} [DecidableEq Role]
    (policy : PreAnswerRolePolicy Role) (limits : OracleLimits)
    (actor : QueryActor) (state : PersistentRoleOracleState Role)
    (programming : Programming) :
    (programOracleWithPreAnswerRoles policy limits actor state programming).map
        (fun result => result.1.oracle) =
      programOracle limits actor state.oracle programming := by
  simp only [programOracleWithPreAnswerRoles,
    prepare_persistent_role_input_oracle]
  cases programOracle limits actor state.oracle programming <;> rfl

theorem successful_preanswer_query_threads_roles
    {Role : Type u} [DecidableEq Role]
    (policy : PreAnswerRolePolicy Role)
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : PersistentRoleOracleState Role)
    (input : ShaInput) (output : ShaOutput)
    (observation : Option (PersistentRoleObservation Role))
    (success : queryOracleWithPreAnswerRoles policy controller limits actor
      state input = .ok (output, nextState, observation)) :
    nextState.roles = (preparePersistentRoleInput policy state input).roles := by
  simp only [queryOracleWithPreAnswerRoles,
    prepare_persistent_role_input_oracle] at success
  cases queried : queryOracle controller limits actor state.oracle input with
  | error reason => simp [queried] at success
  | ok pair =>
      rcases pair with ⟨actual, nextOracle⟩
      simp only [queried, Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl, rfl⟩
      rfl

theorem successful_preanswer_program_threads_roles
    {Role : Type u} [DecidableEq Role]
    (policy : PreAnswerRolePolicy Role) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : PersistentRoleOracleState Role)
    (programming : Programming)
    (observation : Option (PersistentRoleObservation Role))
    (success : programOracleWithPreAnswerRoles policy limits actor state
      programming = .ok (nextState, observation)) :
    nextState.roles =
      (preparePersistentRoleInput policy state programming.input).roles := by
  simp only [programOracleWithPreAnswerRoles,
    prepare_persistent_role_input_oracle] at success
  cases programmed : programOracle limits actor state.oracle programming with
  | error reason => simp [programmed] at success
  | ok nextOracle =>
      simp only [programmed, Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      rfl

/-- If a successful query is a cache hit, any reported role was already bound
before the policy ran.  The policy cannot infer it retrospectively from the
cached answer. -/
theorem cached_reuse_observation_was_previously_bound
    {Role : Type u} [DecidableEq Role]
    (policy : PreAnswerRolePolicy Role)
    (state : PersistentRoleOracleState Role) (input : ShaInput)
    (entry : TableEntry) (output : ShaOutput)
    (observation : PersistentRoleObservation Role)
    (found : lookupEntry state.oracle input = some entry)
    (observed : queryRoleObservation?
      (preparePersistentRoleInput policy state input).roles state.oracle input
        output = some observation) :
    state.roles.roleForInput? input = some observation.role := by
  rw [prepare_existing_input_preserves_roles policy state input entry found]
    at observed
  unfold queryRoleObservation? at observed
  cases selected : state.roles.roleForInput? input with
  | none => simp [selected] at observed
  | some role =>
      simp only [selected, Option.map_some, Option.some.injEq] at observed
      cases observed
      simpa using selected

/-! ## Stateful executable pre-answer automaton -/

/-- A genuine pre-answer automaton.  `classify` cannot inspect the current
answer.  Only `afterQuery` and `afterProgramming` receive the completed
operation and may update control for later inputs. -/
structure ExecutablePreAnswerRolePolicy
    (Control : Type u) (Role : Type u) where
  classify : Control → QueryActor → OracleState → ShaInput → Option Role
  afterQuery : Control → QueryActor → OracleState → ShaInput → ShaOutput →
    OracleState → Control
  afterProgramming : Control → QueryActor → OracleState → Programming →
    OracleState → Control

structure PersistentRoleMachineState
    (Control : Type u) (Role : Type u) where
  control : Control
  oracle : OracleState
  roles : PersistentTranscriptRoles Role

def prepareExecutableRoleInput
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (actor : QueryActor) (state : PersistentRoleMachineState Control Role)
    (input : ShaInput) : PersistentRoleMachineState Control Role :=
  let base : PersistentRoleOracleState Role :=
    { oracle := state.oracle, roles := state.roles }
  let prepared := preparePersistentRoleInput
    (fun _ oracle currentInput =>
      policy.classify state.control actor oracle currentInput)
    base input
  { control := state.control
    oracle := prepared.oracle
    roles := prepared.roles }

@[simp] theorem prepare_executable_role_input_oracle
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (actor : QueryActor) (state : PersistentRoleMachineState Control Role)
    (input : ShaInput) :
    (prepareExecutableRoleInput policy actor state input).oracle =
      state.oracle := by
  exact prepare_persistent_role_input_oracle _ _ _

@[simp] theorem prepare_executable_role_input_control
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (actor : QueryActor) (state : PersistentRoleMachineState Control Role)
    (input : ShaInput) :
    (prepareExecutableRoleInput policy actor state input).control =
      state.control := by
  rfl

theorem prepare_executable_existing_input_preserves_roles
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (actor : QueryActor) (state : PersistentRoleMachineState Control Role)
    (input : ShaInput) (entry : TableEntry)
    (found : lookupEntry state.oracle input = some entry) :
    (prepareExecutableRoleInput policy actor state input).roles =
      state.roles := by
  exact prepare_existing_input_preserves_roles _
    ({ oracle := state.oracle, roles := state.roles } :
      PersistentRoleOracleState Role) input entry found

def queryOracleWithExecutableRoles
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state : PersistentRoleMachineState Control Role)
    (input : ShaInput) :
    Except OracleAbort
      (ShaOutput × PersistentRoleMachineState Control Role ×
        Option (PersistentRoleObservation Role)) :=
  let prepared := prepareExecutableRoleInput policy actor state input
  match queryOracle controller limits actor prepared.oracle input with
  | .error reason => .error reason
  | .ok (output, nextOracle) =>
      .ok (output,
        { control := policy.afterQuery prepared.control actor prepared.oracle
            input output nextOracle
          oracle := nextOracle
          roles := prepared.roles },
        queryRoleObservation? prepared.roles prepared.oracle input output)

def programOracleWithExecutableRoles
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (limits : OracleLimits) (actor : QueryActor)
    (state : PersistentRoleMachineState Control Role)
    (programming : Programming) :
    Except OracleAbort
      (PersistentRoleMachineState Control Role ×
        Option (PersistentRoleObservation Role)) :=
  let prepared := prepareExecutableRoleInput policy actor state
    programming.input
  match programOracle limits actor prepared.oracle programming with
  | .error reason => .error reason
  | .ok nextOracle =>
      .ok
        ({ control := policy.afterProgramming prepared.control actor
              prepared.oracle programming nextOracle
           oracle := nextOracle
           roles := prepared.roles },
          programmingRoleObservation? prepared.roles programming)

theorem query_oracle_with_executable_roles_erases
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state : PersistentRoleMachineState Control Role)
    (input : ShaInput) :
    (queryOracleWithExecutableRoles policy controller limits actor state input).map
        (fun result => (result.1, result.2.1.oracle)) =
      queryOracle controller limits actor state.oracle input := by
  simp only [queryOracleWithExecutableRoles,
    prepare_executable_role_input_oracle]
  cases queryOracle controller limits actor state.oracle input <;> rfl

theorem program_oracle_with_executable_roles_erases
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (limits : OracleLimits) (actor : QueryActor)
    (state : PersistentRoleMachineState Control Role)
    (programming : Programming) :
    (programOracleWithExecutableRoles policy limits actor state programming).map
        (fun result => result.1.oracle) =
      programOracle limits actor state.oracle programming := by
  simp only [programOracleWithExecutableRoles,
    prepare_executable_role_input_oracle]
  cases programOracle limits actor state.oracle programming <;> rfl

theorem successful_executable_query_threads_preanswer_roles
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor)
    (state nextState : PersistentRoleMachineState Control Role)
    (input : ShaInput) (output : ShaOutput)
    (observation : Option (PersistentRoleObservation Role))
    (success : queryOracleWithExecutableRoles policy controller limits actor
      state input = .ok (output, nextState, observation)) :
    nextState.roles =
      (prepareExecutableRoleInput policy actor state input).roles := by
  simp only [queryOracleWithExecutableRoles,
    prepare_executable_role_input_oracle] at success
  cases queried : queryOracle controller limits actor state.oracle input with
  | error reason => simp [queried] at success
  | ok pair =>
      rcases pair with ⟨actual, nextOracle⟩
      simp only [queried, Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl, rfl⟩
      rfl

theorem successful_executable_program_threads_preanswer_roles
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (limits : OracleLimits) (actor : QueryActor)
    (state nextState : PersistentRoleMachineState Control Role)
    (programming : Programming)
    (observation : Option (PersistentRoleObservation Role))
    (success : programOracleWithExecutableRoles policy limits actor state
      programming = .ok (nextState, observation)) :
    nextState.roles =
      (prepareExecutableRoleInput policy actor state
        programming.input).roles := by
  simp only [programOracleWithExecutableRoles,
    prepare_executable_role_input_oracle] at success
  cases programmed : programOracle limits actor state.oracle programming with
  | error reason => simp [programmed] at success
  | ok nextOracle =>
      simp only [programmed, Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      rfl

/-- A cached call whose input was unbound before the call stays unbound after
the call.  This is the executable no-retrospective-assignment theorem. -/
theorem cached_unbound_query_remains_unbound
    {Control Role : Type u} [DecidableEq Role]
    (policy : ExecutablePreAnswerRolePolicy Control Role)
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor)
    (state nextState : PersistentRoleMachineState Control Role)
    (input : ShaInput) (entry : TableEntry) (output : ShaOutput)
    (observation : Option (PersistentRoleObservation Role))
    (unbound : state.roles.roleForInput? input = none)
    (found : lookupEntry state.oracle input = some entry)
    (success : queryOracleWithExecutableRoles policy controller limits actor
      state input = .ok (output, nextState, observation)) :
    nextState.roles.roleForInput? input = none := by
  rw [successful_executable_query_threads_preanswer_roles policy controller
    limits actor state nextState input output observation success,
    prepare_executable_existing_input_preserves_roles policy actor state input
      entry found]
  exact unbound

theorem executable_cached_observation_was_previously_bound
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
    state.roles.roleForInput? input = some observation.role := by
  simp only [queryOracleWithExecutableRoles,
    prepare_executable_role_input_oracle] at success
  cases queried : queryOracle controller limits actor state.oracle input with
  | error reason => simp [queried] at success
  | ok pair =>
      rcases pair with ⟨actual, nextOracle⟩
      simp only [queried, Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl, observationExact⟩
      exact cached_reuse_observation_was_previously_bound
        (fun _ oracle currentInput =>
          policy.classify state.control actor oracle currentInput)
        ({ oracle := state.oracle, roles := state.roles } :
          PersistentRoleOracleState Role)
        input entry actual observation found observationExact

/-! ## Exact generic selection obstruction -/

/-- When two continuations compatible with the same pre-answer view require
different eventual roles, no deterministic pre-answer classifier can be exact
for both.  A source theorem must rule out one continuation or provide an
earlier distinguishing control state; completed future context cannot be used
to choose between them. -/
theorem no_preanswer_classifier_selects_two_distinct_future_roles
    {View Continuation Role : Type u}
    (classify : View → Option Role) (eventual : Continuation → Role)
    (view : View) (left right : Continuation)
    (different : eventual left ≠ eventual right) :
    ¬ (classify view = some (eventual left) ∧
        classify view = some (eventual right)) := by
  rintro ⟨leftExact, rightExact⟩
  exact different (Option.some.inj (leftExact.symm.trans rightExact))

/-- A query result instrumented with a persistent role observation. -/
def queryOracleWithPersistentRoles {Role : Type u}
    (roles : PersistentTranscriptRoles Role)
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state : OracleState) (input : ShaInput) :
    Except OracleAbort
      (ShaOutput × OracleState × Option (PersistentRoleObservation Role)) :=
  match queryOracle controller limits actor state input with
  | .error reason => .error reason
  | .ok (output, nextState) =>
      .ok (output, nextState,
        queryRoleObservation? roles state input output)

/-- A programming result instrumented with a persistent role observation. -/
def programOracleWithPersistentRoles {Role : Type u}
    (roles : PersistentTranscriptRoles Role) (limits : OracleLimits)
    (actor : QueryActor) (state : OracleState) (programming : Programming) :
    Except OracleAbort
      (OracleState × Option (PersistentRoleObservation Role)) :=
  match programOracle limits actor state programming with
  | .error reason => .error reason
  | .ok nextState =>
      .ok (nextState, programmingRoleObservation? roles programming)

/-- Erasing the observation is definitionally the production query. -/
theorem query_oracle_with_persistent_roles_erases
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state : OracleState) (input : ShaInput) :
    (queryOracleWithPersistentRoles roles controller limits actor state input).map
        (fun result => (result.1, result.2.1)) =
      queryOracle controller limits actor state input := by
  unfold queryOracleWithPersistentRoles
  cases queryOracle controller limits actor state input <;> rfl

/-- Erasing the observation is definitionally the production programming
operation. -/
theorem program_oracle_with_persistent_roles_erases
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (limits : OracleLimits) (actor : QueryActor) (state : OracleState)
    (programming : Programming) :
    (programOracleWithPersistentRoles roles limits actor state programming).map
        Prod.fst =
      programOracle limits actor state programming := by
  unfold programOracleWithPersistentRoles
  cases programOracle limits actor state programming <;> rfl

/-- A successful tracked query at a role-bound missing input is classified as
its first fresh exposure, and the literal operational history appends the
matching fresh record. -/
theorem tracked_query_missing_is_exact_fresh_exposure
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (role : Role) (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (output : ShaOutput)
    (bound : roles.roleForInput? input = some role)
    (missing : lookupEntry state input = none)
    (success : queryOracleWithPersistentRoles roles controller limits actor
      state input = .ok (output, nextState,
        some { role := role
               input := input
               output := output
               use := .fresh })) :
    ∃ record : QueryRecord,
      nextState.history = state.history ++ [record] ∧
        record.input = input ∧ record.output = output ∧
        record.actor = actor ∧ record.origin = .fresh := by
  have _boundBeforeAnswer : roles.roleForInput? input = some role := bound
  by_cases totalBlocked : state.totalCalls ≥ limits.totalCalls
  · simp [queryOracleWithPersistentRoles, queryOracle, totalBlocked] at success
  by_cases freshBlocked : state.freshCalls ≥ limits.freshCalls
  · simp [queryOracleWithPersistentRoles, queryOracle, totalBlocked, missing,
      freshBlocked] at success
  cases decided : controller state.history input with
  | refuse =>
      simp [queryOracleWithPersistentRoles, queryOracle, totalBlocked, missing,
        freshBlocked, decided] at success
  | answer answer =>
      simp only [queryOracleWithPersistentRoles, queryOracle, totalBlocked,
        ↓reduceIte, missing, freshBlocked, decided, Except.ok.injEq,
        Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl, _observation⟩
      exact ⟨
        { input := input
          output := answer
          actor := actor
          origin := .fresh },
        rfl, rfl, rfl, rfl, rfl⟩

/-- A successful tracked query at an existing entry is exactly cached from
that entry's source and returns its stored output. -/
theorem tracked_query_existing_is_exact_cached_reuse
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (role : Role) (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (entry : TableEntry)
    (bound : roles.roleForInput? input = some role)
    (found : lookupEntry state input = some entry)
    (success : queryOracle controller limits actor state input =
      .ok (entry.output, nextState)) :
    queryOracleWithPersistentRoles roles controller limits actor state input =
      .ok (entry.output, nextState,
        some { role := role
               input := input
               output := entry.output
               use := .cached entry.source }) := by
  simp [queryOracleWithPersistentRoles, success, queryRoleObservation?, bound,
    found]

/-- A successful tracked programming operation is exactly a programmed first
exposure and appends the literal production programming record and table
entry. -/
theorem tracked_program_is_exact_programmed_exposure
    {Role : Type u} (roles : PersistentTranscriptRoles Role)
    (role : Role) (limits : OracleLimits) (actor : QueryActor)
    (state nextState : OracleState) (programming : Programming)
    (bound : roles.roleForInput? programming.input = some role)
    (success : programOracle limits actor state programming = .ok nextState) :
    programOracleWithPersistentRoles roles limits actor state programming =
        .ok (nextState,
          some { role := role
                 input := programming.input
                 output := programming.output
                 use := .programmed }) ∧
      nextState.history = state.history ∧
      nextState.programmingHistory = state.programmingHistory ++
        [{ input := programming.input
           output := programming.output
           actor := actor }] ∧
      nextState.table = state.table ++
        [{ input := programming.input
           output := programming.output
           source := .programmed }] := by
  have exact := AspisK1.V7Tag73AtomicPairReplay.program_oracle_success_exact
    limits actor state nextState programming success
  refine ⟨?_, exact.1, exact.2.1, exact.2.2.1⟩
  simp [programOracleWithPersistentRoles, success,
    programmingRoleObservation?, bound]

#print axioms guarded_install_rejects_existing_table_entry
#print axioms guarded_install_rejects_bound_role
#print axioms guarded_install_rejects_bound_input
#print axioms guarded_install_success_binds_exact_input
#print axioms prepare_existing_input_preserves_roles
#print axioms query_oracle_with_preanswer_roles_erases
#print axioms program_oracle_with_preanswer_roles_erases
#print axioms cached_reuse_observation_was_previously_bound
#print axioms prepare_executable_existing_input_preserves_roles
#print axioms query_oracle_with_executable_roles_erases
#print axioms program_oracle_with_executable_roles_erases
#print axioms successful_executable_query_threads_preanswer_roles
#print axioms successful_executable_program_threads_preanswer_roles
#print axioms cached_unbound_query_remains_unbound
#print axioms executable_cached_observation_was_previously_bound
#print axioms no_preanswer_classifier_selects_two_distinct_future_roles
#print axioms query_oracle_with_persistent_roles_erases
#print axioms program_oracle_with_persistent_roles_erases
#print axioms tracked_query_missing_is_exact_fresh_exposure
#print axioms tracked_query_existing_is_exact_cached_reuse
#print axioms tracked_program_is_exact_programmed_exposure

end

end AspisK1.V7Tag73PersistentTranscriptRoles
