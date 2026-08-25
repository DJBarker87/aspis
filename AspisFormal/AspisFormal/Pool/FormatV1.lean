import Mathlib

/-!
# Pool V1 format freeze

This module records the version identifiers used by the pure Pool V1 Rust
kernel.  The numbers name already-frozen Aspis primitives; they do not replace
the cryptographic definitions or authorize an on-chain verifier.
-/

set_option autoImplicit false

namespace AspisPool.FormatV1

structure Binding where
  poolFormat : Nat
  noteCommitment : Nat
  nullifier : Nat
  treeHash : Nat
  digestEncoding : Nat
  treeDepth : Nat
  rootHistoryCapacityLog2 : Nat
  identity : Nat
  verifierPolicy : Nat
  verifierRegistry : Nat
  verifierEntry : Nat
  treeState : Nat
  rootHistory : Nat
  deriving DecidableEq, Repr

/-- Exact semantic-format tuple mirrored by `POOL_V1_FORMAT_BINDING`. -/
def binding : Binding where
  poolFormat := 2
  noteCommitment := 2
  nullifier := 1
  treeHash := 3
  digestEncoding := 1
  treeDepth := 20
  rootHistoryCapacityLog2 := 8
  identity := 1
  verifierPolicy := 1
  verifierRegistry := 1
  verifierEntry := 1
  treeState := 1
  rootHistory := 1

/-- Exact 32-byte binding image, represented as natural bytes. -/
def bindingBytes : List Nat :=
  [65, 83, 80, 80, 79, 79, 76, 49,
   2, 2, 1, 3, 1, 20, 8, 1, 1, 1, 1, 1, 1,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def treeCapacity : Nat := 2 ^ binding.treeDepth
def rootHistoryPageCapacity : Nat := 2 ^ binding.rootHistoryCapacityLog2

def identityAccountBytes : Nat := 144
def verifierPolicyBytes : Nat := 104
def verifierRegistryBytes : Nat := 128
def verifierEntryBytes : Nat := 192
def treeStateAccountBytes : Nat := 48 + 32 * binding.treeDepth
def rootHistoryHeaderBytes : Nat := 64
def rootHistoryPageAccountBytes : Nat :=
  rootHistoryHeaderBytes + 32 * rootHistoryPageCapacity

theorem binding_exact :
    binding = ⟨2, 2, 1, 3, 1, 20, 8, 1, 1, 1, 1, 1, 1⟩ := rfl

theorem bindingBytes_length : bindingBytes.length = 32 := by
  norm_num [bindingBytes]

theorem bindingBytes_are_bytes : ∀ byte ∈ bindingBytes, byte < 256 := by
  norm_num [bindingBytes]

theorem exact_capacities :
    treeCapacity = 1_048_576 ∧ rootHistoryPageCapacity = 256 := by
  norm_num [treeCapacity, rootHistoryPageCapacity, binding]

theorem exact_account_image_sizes :
    identityAccountBytes = 144 ∧
    verifierPolicyBytes = 104 ∧
    verifierRegistryBytes = 128 ∧
    verifierEntryBytes = 192 ∧
    treeStateAccountBytes = 688 ∧
    rootHistoryPageAccountBytes = 8_256 := by
  norm_num [identityAccountBytes, verifierPolicyBytes,
    verifierRegistryBytes, verifierEntryBytes,
    treeStateAccountBytes, rootHistoryPageAccountBytes,
    rootHistoryHeaderBytes, rootHistoryPageCapacity, binding]

#print axioms binding_exact
#print axioms bindingBytes_length
#print axioms bindingBytes_are_bytes
#print axioms exact_capacities
#print axioms exact_account_image_sizes

end AspisPool.FormatV1
