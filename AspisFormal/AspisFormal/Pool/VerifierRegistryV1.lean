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
#print axioms no_registry_entry_implies_no_spend_state_change
#print axioms exact_registry_account_sizes

end AspisPool.VerifierRegistryV1
