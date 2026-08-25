import Mathlib
import AspisFormal.Pool.FormatV1

/-!
# Pool V1 multi-profile verifier registry

This is the pure authorization model for the P0 registry format. It proves
that acceptance names one exact active verifier/profile/release for one Pool,
and that adding or retiring registry entries cannot alter the stable Pool
identity, tree or vault. Solana PDA/owner parsing, governance, CPI and verifier
return-data authentication remain source/runtime boundaries.
-/

set_option autoImplicit false

namespace AspisPool.VerifierRegistryV1

inductive EntryStatus where
  | pending
  | active
  | paused
  | retired
  deriving DecidableEq, Repr

structure Policy where
  registryProgram : Nat
  registryAuthority : Nat
  policyBinding : Nat
  immutable : Bool
  deriving DecidableEq, Repr

structure Registry where
  pool : Nat
  registryProgram : Nat
  authority : Nat
  policyBinding : Nat
  immutable : Bool
  paused : Bool
  generation : Nat
  minimumActivationDelaySlots : Nat
  deriving DecidableEq, Repr

structure Entry where
  pool : Nat
  verifierProgram : Nat
  profileBinding : Nat
  releaseBinding : Nat
  statementVersion : Nat
  activationSlot : Nat
  retirementSlot : Option Nat
  policyBinding : Nat
  status : EntryStatus
  deriving DecidableEq, Repr

structure Selection where
  verifierProgram : Nat
  profileBinding : Nat
  releaseBinding : Nat
  statementVersion : Nat
  deriving DecidableEq, Repr

def ActiveAt (entry : Entry) (slot : Nat) : Prop :=
  entry.status = .active ∧
    entry.activationSlot ≤ slot ∧
      ∀ retirement, entry.retirementSlot = some retirement → slot < retirement

/-- Pure counterpart of the fail-closed Rust acceptance order. -/
def Authorized (pool : Nat) (policy : Policy) (registry : Registry)
    (entry : Entry) (selection : Selection) (slot : Nat) : Prop :=
  registry.pool = pool ∧
    registry.registryProgram = policy.registryProgram ∧
    registry.authority = policy.registryAuthority ∧
    registry.policyBinding = policy.policyBinding ∧
    registry.immutable = policy.immutable ∧
    registry.paused = false ∧
    entry.pool = pool ∧
    entry.policyBinding = policy.policyBinding ∧
    entry.verifierProgram = selection.verifierProgram ∧
    entry.profileBinding = selection.profileBinding ∧
    entry.releaseBinding = selection.releaseBinding ∧
    entry.statementVersion = selection.statementVersion ∧
    ActiveAt entry slot

theorem accepted_entry_is_exact_and_active (pool : Nat) (policy : Policy)
    (registry : Registry) (entry : Entry) (selection : Selection) (slot : Nat)
    (accepted : Authorized pool policy registry entry selection slot) :
    entry.verifierProgram = selection.verifierProgram ∧
      entry.profileBinding = selection.profileBinding ∧
      entry.releaseBinding = selection.releaseBinding ∧
      entry.statementVersion = selection.statementVersion ∧
      ActiveAt entry slot := by
  rcases accepted with
    ⟨_, _, _, _, _, _, _, _, verifier, profile, release, statement, active⟩
  exact ⟨verifier, profile, release, statement, active⟩

theorem accepted_spend_binds_entry_and_pool (pool : Nat) (policy : Policy)
    (registry : Registry) (entry : Entry) (selection : Selection) (slot : Nat)
    (accepted : Authorized pool policy registry entry selection slot) :
    registry.pool = pool ∧
      entry.pool = pool ∧
      registry.policyBinding = policy.policyBinding ∧
      entry.policyBinding = policy.policyBinding := by
  rcases accepted with ⟨registryPool, _, _, registryPolicy, _, _, entryPool,
    entryPolicy, _⟩
  exact ⟨registryPool, entryPool, registryPolicy, entryPolicy⟩

structure StablePoolState (Tree Vault : Type) where
  poolIdentity : Nat
  tree : Tree
  vault : Vault
  deriving DecidableEq

structure SystemState (Tree Vault : Type) where
  pool : StablePoolState Tree Vault
  entries : List Entry
  deriving DecidableEq

def addProfile {Tree Vault : Type} (state : SystemState Tree Vault)
    (entry : Entry) : SystemState Tree Vault :=
  { state with entries := entry :: state.entries }

theorem adding_profile_preserves_pool_identity {Tree Vault : Type}
    (state : SystemState Tree Vault) (entry : Entry) :
    (addProfile state entry).pool.poolIdentity = state.pool.poolIdentity := rfl

theorem adding_profile_preserves_tree_and_vault {Tree Vault : Type}
    (state : SystemState Tree Vault) (entry : Entry) :
    (addProfile state entry).pool.tree = state.pool.tree ∧
      (addProfile state entry).pool.vault = state.pool.vault := by
  exact ⟨rfl, rfl⟩

def retireEntry (profileBinding releaseBinding : Nat) (entry : Entry) : Entry :=
  if entry.profileBinding = profileBinding ∧ entry.releaseBinding = releaseBinding then
    { entry with status := .retired }
  else
    entry

def retireProfile {Tree Vault : Type} (state : SystemState Tree Vault)
    (profileBinding releaseBinding : Nat) : SystemState Tree Vault :=
  { state with
    entries := state.entries.map (retireEntry profileBinding releaseBinding) }

theorem retiring_profile_does_not_reinterpret_existing_state {Tree Vault : Type}
    (state : SystemState Tree Vault) (profileBinding releaseBinding : Nat) :
    (retireProfile state profileBinding releaseBinding).pool = state.pool := rfl

/-! ## Governance scheduling and continuity -/

/-- A newly scheduled entry is pending, belongs to this Pool/policy and cannot
become active before the registry's configured delay has elapsed. -/
def ScheduledAt (registry : Registry) (now : Nat) (entry : Entry) : Prop :=
  registry.minimumActivationDelaySlots > 0 ∧
    entry.status = .pending ∧
    entry.pool = registry.pool ∧
    entry.policyBinding = registry.policyBinding ∧
    now + registry.minimumActivationDelaySlots ≤ entry.activationSlot

theorem scheduled_activation_respects_nonzero_delay
    (registry : Registry) (now : Nat) (entry : Entry)
    (scheduled : ScheduledAt registry now entry) :
    now < entry.activationSlot := by
  rcases scheduled with ⟨delayPositive, _, _, _, scheduledAt⟩
  omega

/-- Activation is a status-only transition and is legal only after the exact
scheduled slot. -/
def activateAt (slot : Nat) (entry : Entry) : Option Entry :=
  if entry.status = .pending ∧ entry.activationSlot ≤ slot then
    some { entry with status := .active }
  else
    none

theorem activation_cannot_precede_scheduled_slot
    (slot : Nat) (entry activated : Entry)
    (run : activateAt slot entry = some activated) :
    entry.activationSlot ≤ slot ∧
      activated = { entry with status := .active } := by
  simp only [activateAt] at run
  split at run
  · rename_i legal
    exact ⟨legal.2, Option.some.inj run |>.symm⟩
  · simp at run

/-- Compatibility is supplied by the policy-bound release manifest. The
on-chain entry identifies that manifest by profile/release/policy bindings;
the governance source bridge must authenticate it rather than inventing a
second cryptographic relation here. -/
def ExactRetirementContinuity (Compatible : Entry → Prop) (slot : Nat)
    (retiring replacement : Entry) : Prop :=
  (retiring.profileBinding ≠ replacement.profileBinding ∨
      retiring.releaseBinding ≠ replacement.releaseBinding) ∧
    Compatible retiring ∧
    Compatible replacement ∧
    replacement.pool = retiring.pool ∧
    replacement.policyBinding = retiring.policyBinding ∧
    ActiveAt replacement slot

theorem retirement_requires_distinct_active_compatible_replacement
    (Compatible : Entry → Prop) (slot : Nat) (retiring replacement : Entry)
    (continuity : ExactRetirementContinuity Compatible slot retiring replacement) :
    (retiring.profileBinding ≠ replacement.profileBinding ∨
        retiring.releaseBinding ≠ replacement.releaseBinding) ∧
      Compatible replacement ∧
      replacement.pool = retiring.pool ∧
      replacement.policyBinding = retiring.policyBinding ∧
      ActiveAt replacement slot := by
  exact ⟨continuity.1, continuity.2.2.1, continuity.2.2.2.1,
    continuity.2.2.2.2.1, continuity.2.2.2.2.2⟩

structure GovernedSystemState (Tree Vault : Type) where
  pool : StablePoolState Tree Vault
  registry : Registry
  entries : List Entry
  deriving DecidableEq

def setRegistryPause {Tree Vault : Type} (state : GovernedSystemState Tree Vault)
    (paused : Bool) : GovernedSystemState Tree Vault :=
  { state with
    registry := { state.registry with
      paused
      generation := state.registry.generation + 1 } }

def scheduleProfile {Tree Vault : Type} (state : GovernedSystemState Tree Vault)
    (entry : Entry) : GovernedSystemState Tree Vault :=
  { state with
    registry := { state.registry with generation := state.registry.generation + 1 }
    entries := entry :: state.entries }

def retireGovernedProfile {Tree Vault : Type}
    (state : GovernedSystemState Tree Vault)
    (profileBinding releaseBinding : Nat) : GovernedSystemState Tree Vault :=
  { state with
    registry := { state.registry with generation := state.registry.generation + 1 }
    entries := state.entries.map (retireEntry profileBinding releaseBinding) }

theorem governance_mutations_preserve_pool_identity_tree_and_vault
    {Tree Vault : Type} (state : GovernedSystemState Tree Vault)
    (entry : Entry) (paused : Bool) (profileBinding releaseBinding : Nat) :
    (setRegistryPause state paused).pool = state.pool ∧
      (scheduleProfile state entry).pool = state.pool ∧
      (retireGovernedProfile state profileBinding releaseBinding).pool = state.pool := by
  exact ⟨rfl, rfl, rfl⟩

theorem governance_mutations_increment_generation_once
    {Tree Vault : Type} (state : GovernedSystemState Tree Vault)
    (entry : Entry) (paused : Bool) (profileBinding releaseBinding : Nat) :
    (setRegistryPause state paused).registry.generation =
        state.registry.generation + 1 ∧
      (scheduleProfile state entry).registry.generation =
        state.registry.generation + 1 ∧
      (retireGovernedProfile state profileBinding releaseBinding).registry.generation =
        state.registry.generation + 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Abstract fail-closed settlement gate: the absence of an authenticated
entry returns the pre-state exactly. The Rust source bridge must prove that no
write occurs before this authorization result exists. -/
def settleAfterRegistry {State : Type} (before candidate : State) :
    Option Entry → State
  | none => before
  | some _ => candidate

theorem no_registry_entry_implies_no_spend_state_change {State : Type}
    (before candidate : State) :
    settleAfterRegistry before candidate none = before := rfl

theorem exact_registry_account_sizes :
    AspisPool.FormatV1.verifierPolicyBytes = 104 ∧
      AspisPool.FormatV1.verifierRegistryBytes = 128 ∧
      AspisPool.FormatV1.verifierEntryBytes = 192 := by
  norm_num [AspisPool.FormatV1.verifierPolicyBytes,
    AspisPool.FormatV1.verifierRegistryBytes,
    AspisPool.FormatV1.verifierEntryBytes]

#print axioms accepted_entry_is_exact_and_active
#print axioms accepted_spend_binds_entry_and_pool
#print axioms adding_profile_preserves_pool_identity
#print axioms adding_profile_preserves_tree_and_vault
#print axioms retiring_profile_does_not_reinterpret_existing_state
#print axioms scheduled_activation_respects_nonzero_delay
#print axioms activation_cannot_precede_scheduled_slot
#print axioms retirement_requires_distinct_active_compatible_replacement
#print axioms governance_mutations_preserve_pool_identity_tree_and_vault
#print axioms governance_mutations_increment_generation_once
#print axioms no_registry_entry_implies_no_spend_state_change
#print axioms exact_registry_account_sizes

end AspisPool.VerifierRegistryV1
