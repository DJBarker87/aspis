import AspisFormal.Pool.VerifierRegistryV1
import AspisFormal.Pool.V7EightLaneCustodySettlement

/-!
# Compact one-transaction dispatch for the eight-lane forest

The canonical ASF8 semantic statement is 1,880 bytes and must not be placed in
the outer Solana transaction or the legacy ASVQ envelope.  ASQ8 carries only
the selected profile/release, Pool program identity and the 216-byte payment
public statement.  The proof account and three canonical read-only Pool
accounts supply the remaining data.  The verifier and Pool reconstruct the
same ASF8 object around the same proof-carried/returned afterstate.

This is the pure reconstruction and size theorem.  Rust byte equality, PDA
derivation, registry account parsing, CPI account privileges and Solana
runtime behavior remain source/runtime obligations.
-/

set_option autoImplicit false

namespace AspisPool.V7EightLaneCompactDispatch

def asq8HeaderBytes : Nat := 8
def paymentPublicBytes : Nat := 216
def asq8IdentityFields : Nat := 3
def identityBytes : Nat := 32
def asq8RequestBytes : Nat :=
  asq8HeaderBytes + asq8IdentityFields * identityBytes + paymentPublicBytes

def asf8CommonBytes : Nat := 144
def pairLateStatementBytes : Nat := 1_520
def asf8SemanticBytes : Nat :=
  asf8CommonBytes + pairLateStatementBytes + paymentPublicBytes

def asr8HeaderBytes : Nat := 8
def asr8IdentityFields : Nat := 3
def pairAfterstateBytes : Nat := 688
def asr8ResultBytes : Nat :=
  asr8HeaderBytes + asr8IdentityFields * identityBytes + pairAfterstateBytes

def solanaReturnDataMaxBytes : Nat := 1_024

structure CompactRequest (Profile Release PoolProgram Payment : Type) where
  profile : Profile
  release : Release
  poolProgram : PoolProgram
  payment : Payment
  deriving DecidableEq

/-- Exact read-only account snapshot consumed by both reconstructions. -/
structure ForestAccountSnapshot
    (ProofAccount MasterAccount CheckpointAccount LaneAccount
      Master Checkpoint Lane : Type) where
  proofAccount : ProofAccount
  masterAccount : MasterAccount
  checkpointAccount : CheckpointAccount
  laneAccount : LaneAccount
  master : Master
  checkpoint : Checkpoint
  lane : Lane
  deriving DecidableEq

/-- Typed form of the complete 1,880-byte ASF8 semantic object. -/
structure SemanticForestStatement
    (Profile Release PoolProgram Payment
      ProofAccount MasterAccount CheckpointAccount LaneAccount
      Master Checkpoint Lane Candidate : Type) where
  request : CompactRequest Profile Release PoolProgram Payment
  snapshot : ForestAccountSnapshot ProofAccount MasterAccount CheckpointAccount
    LaneAccount Master Checkpoint Lane
  candidate : Candidate
  deriving DecidableEq

def reconstructSemanticStatement
    {Profile Release PoolProgram Payment
      ProofAccount MasterAccount CheckpointAccount LaneAccount
      Master Checkpoint Lane Candidate : Type}
    (request : CompactRequest Profile Release PoolProgram Payment)
    (snapshot : ForestAccountSnapshot ProofAccount MasterAccount
      CheckpointAccount LaneAccount Master Checkpoint Lane)
    (candidate : Candidate) :
    SemanticForestStatement Profile Release PoolProgram Payment ProofAccount
      MasterAccount CheckpointAccount LaneAccount Master Checkpoint Lane
      Candidate where
  request := request
  snapshot := snapshot
  candidate := candidate

structure CompactResult
    (MasterAccount LaneAccount Nullifier Candidate : Type) where
  masterAccount : MasterAccount
  laneAccount : LaneAccount
  nullifier : Nullifier
  candidate : Candidate
  deriving DecidableEq

/-- The Pool accepts ASR8 only when its echoed account/nullifier bindings and
candidate are exactly those used in the semantic reconstruction. -/
def ResultAuthenticates
    {MasterAccount LaneAccount Nullifier Candidate : Type}
    (expectedMaster : MasterAccount)
    (expectedLane : LaneAccount)
    (expectedNullifier : Nullifier)
    (expectedCandidate : Candidate)
    (result : CompactResult MasterAccount LaneAccount Nullifier Candidate) : Prop :=
  result.masterAccount = expectedMaster ∧
    result.laneAccount = expectedLane ∧
    result.nullifier = expectedNullifier ∧
    result.candidate = expectedCandidate

/-- Central transport theorem: if ASR8 authenticates the candidate and exact
account/nullifier bindings, both sides reconstruct one identical ASF8 semantic
statement without transmitting its 1,880 bytes. -/
theorem authenticated_result_gives_identical_semantic_reconstruction
    {Profile Release PoolProgram Payment
      ProofAccount MasterAccount CheckpointAccount LaneAccount
      Master Checkpoint Lane Nullifier Candidate : Type}
    (request : CompactRequest Profile Release PoolProgram Payment)
    (snapshot : ForestAccountSnapshot ProofAccount MasterAccount
      CheckpointAccount LaneAccount Master Checkpoint Lane)
    (nullifier : Nullifier)
    (provedCandidate : Candidate)
    (result : CompactResult MasterAccount LaneAccount Nullifier Candidate)
    (authenticated : ResultAuthenticates snapshot.masterAccount
      snapshot.laneAccount nullifier provedCandidate result) :
    reconstructSemanticStatement request snapshot provedCandidate =
      reconstructSemanticStatement request snapshot result.candidate := by
  exact congrArg (reconstructSemanticStatement request snapshot)
    authenticated.2.2.2.symm

theorem authenticated_result_echoes_exact_state_bindings
    {MasterAccount LaneAccount Nullifier Candidate : Type}
    (expectedMaster : MasterAccount)
    (expectedLane : LaneAccount)
    (expectedNullifier : Nullifier)
    (expectedCandidate : Candidate)
    (result : CompactResult MasterAccount LaneAccount Nullifier Candidate)
    (authenticated : ResultAuthenticates expectedMaster expectedLane
      expectedNullifier expectedCandidate result) :
    result.masterAccount = expectedMaster ∧
      result.laneAccount = expectedLane ∧
      result.nullifier = expectedNullifier ∧
      result.candidate = expectedCandidate :=
  authenticated

theorem exact_compact_transport_sizes :
    asq8RequestBytes = 320 ∧
      asf8SemanticBytes = 1_880 ∧
      asr8ResultBytes = 792 ∧
      asr8ResultBytes ≤ solanaReturnDataMaxBytes := by
  norm_num [asq8RequestBytes, asq8HeaderBytes, asq8IdentityFields,
    identityBytes, paymentPublicBytes, asf8SemanticBytes, asf8CommonBytes,
    pairLateStatementBytes, asr8ResultBytes, asr8HeaderBytes,
    asr8IdentityFields, pairAfterstateBytes, solanaReturnDataMaxBytes]

/-- The semantic object is deliberately not the CPI wire: reconstruction
removes 1,560 transmitted bytes while retaining every typed field. -/
theorem exact_reconstruction_saves_wire_bytes :
    asf8SemanticBytes - asq8RequestBytes = 1_560 := by
  norm_num [asf8SemanticBytes, asf8CommonBytes, pairLateStatementBytes,
    paymentPublicBytes, asq8RequestBytes, asq8HeaderBytes, asq8IdentityFields,
    identityBytes]

#print axioms authenticated_result_gives_identical_semantic_reconstruction
#print axioms authenticated_result_echoes_exact_state_bindings
#print axioms exact_compact_transport_sizes
#print axioms exact_reconstruction_saves_wire_bytes

end AspisPool.V7EightLaneCompactDispatch
