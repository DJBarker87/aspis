import VerifierRegistryDecoders.Funs
import VerifierRegistryReadonly.Funs
import AspisFormal.Pool.AuthorizationReceiptV1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisPool.VerifierRegistrySourceBridge

open VerifierRegistryDecodersGenerated
open AspisPool.VerifierRegistryV1

noncomputable section

local instance {T : Type} : DecidableEq T := Classical.decEq T
local instance {proposition : Prop} : Decidable proposition :=
  Classical.propDecidable proposition

abbrev Bytes32 := Array Std.U8 32#usize
abbrev GeneratedPolicy := pool_v1.format.VerifierPolicyV1
abbrev GeneratedRegistry := pool_v1.verifier_registry.VerifierRegistryV1
abbrev GeneratedEntry := pool_v1.verifier_registry.VerifierRegistryEntryV1

/-- The read-only part of Solana `AccountInfo` consumed by `registry.rs`.
The production type additionally carries lamports, rent epoch and interior
borrow machinery, none of which is read by this authorization path. -/
structure AccountView where
  key : Bytes32
  owner : Bytes32
  executable : Bool
  isWritable : Bool
  isSigner : Bool

/-- The two runtime operations intentionally left outside this source proof.
`findProgramAddress` receives the literal seed byte strings in production
order. `tryBorrowData` represents one successful or failed immutable Solana
account-data borrow. -/
structure SolanaBoundaries where
  findProgramAddress : List (List Std.U8) → Bytes32 → Bytes32
  tryBorrowData : AccountView → Option (Slice Std.U8)

structure GeneratedSelection where
  verifierProgram : Bytes32
  profileBinding : Bytes32
  releaseBinding : Bytes32
  statementVersion : Std.U8

structure GeneratedAuthenticated where
  policy : GeneratedPolicy
  pool : Bytes32
  verifierProgram : Bytes32
  profileBinding : Bytes32
  releaseBinding : Bytes32
  statementVersion : Std.U8
  registryGeneration : Std.U64
  authenticatedAtSlot : Std.U64

def registrySeed : List Std.U8 :=
  [97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 118#u8, 101#u8,
    114#u8, 105#u8, 102#u8, 105#u8, 101#u8, 114#u8, 45#u8, 114#u8,
    101#u8, 103#u8, 105#u8, 115#u8, 116#u8, 114#u8, 121#u8, 45#u8,
    118#u8, 49#u8]

def entrySeed : List Std.U8 :=
  [97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 118#u8, 101#u8,
    114#u8, 105#u8, 102#u8, 105#u8, 101#u8, 114#u8, 45#u8, 101#u8,
    110#u8, 116#u8, 114#u8, 121#u8, 45#u8, 118#u8, 49#u8]

def registryPda (runtime : SolanaBoundaries) (policy : GeneratedPolicy)
    (pool : Bytes32) : Bytes32 :=
  runtime.findProgramAddress [registrySeed, pool.val] policy.registry_program

def entryPda (runtime : SolanaBoundaries) (policy : GeneratedPolicy)
    (pool : Bytes32) (selection : GeneratedSelection) : Bytes32 :=
  runtime.findProgramAddress
    [entrySeed, pool.val, selection.profileBinding.val,
      selection.releaseBinding.val]
    policy.registry_program

def resultValue {T : Type} : Result T → Option T
  | .ok value => some value
  | .fail _ => none
  | .div => none

def decodedValue {T E : Type} : Result (core.result.Result T E) → Option T
  | .ok (.Ok value) => some value
  | _ => none

def ReadonlyOwned (account : AccountView) (owner : Bytes32) : Prop :=
  account.owner = owner ∧
    account.executable = false ∧
    account.isWritable = false ∧
    account.isSigner = false

def productionAccountOfView (account : AccountView) :
    VerifierRegistryReadonlyGenerated.solana_account_info.AccountInfo where
  key := account.key
  lamports := 0#u64
  data := Array.to_slice (Array.make 0#usize [])
  owner := account.owner
  rent_epoch := 0#u64
  is_signer := account.isSigner
  is_writable := account.isWritable
  executable := account.executable

def productionReadonlyResult (account : AccountView) (owner : Bytes32)
    (invalid : VerifierRegistryReadonlyGenerated.error.PoolV1ProgramError) :
    Option Unit :=
  decodedValue
    (VerifierRegistryReadonlyGenerated.registry.require_readonly_registry_account
      (productionAccountOfView account) owner invalid)

theorem production_readonly_success_iff (account : AccountView) (owner : Bytes32)
    (invalid : VerifierRegistryReadonlyGenerated.error.PoolV1ProgramError) :
    productionReadonlyResult account owner invalid = some () ↔
      ReadonlyOwned account owner := by
  by_cases ownerExact : account.owner = owner
  all_goals cases executableExact : account.executable
  all_goals cases writableExact : account.isWritable
  all_goals cases signerExact : account.isSigner
  all_goals simp [productionReadonlyResult,
    VerifierRegistryReadonlyGenerated.registry.require_readonly_registry_account,
    VerifierRegistryReadonlyGenerated.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq,
    VerifierRegistryReadonlyGenerated.solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from,
    core.cmp.impls.PartialEqShared.ne, core.cmp.PartialEq.ne.default,
    core.convert.IntoFrom.into, productionAccountOfView, decodedValue,
    ReadonlyOwned, ownerExact, executableExact, writableExact, signerExact]

def RegistryChecks (pool : Bytes32) (policy : GeneratedPolicy)
    (registry : GeneratedRegistry) (policyRequiresImmutable immutable paused : Bool) : Prop :=
  registry.pool = pool ∧
    registry.authority = policy.registry_authority ∧
    registry.policy_binding = policy.policy_binding ∧
    immutable = policyRequiresImmutable ∧
    paused = false

def EntryChecks (pool : Bytes32) (policy : GeneratedPolicy)
    (selection : GeneratedSelection) (entry : GeneratedEntry)
    (currentSlot noRetirement : Std.U64) : Prop :=
  entry.pool = pool ∧
    entry.policy_binding = policy.policy_binding ∧
    entry.verifier_program = selection.verifierProgram ∧
    entry.profile_binding = selection.profileBinding ∧
    entry.release_binding = selection.releaseBinding ∧
    entry.statement_version = selection.statementVersion ∧
    entry.status = .Active ∧
    entry.activation_slot.val ≤ currentSlot.val ∧
    (entry.retirement_slot = noRetirement ∨
      currentSlot.val < entry.retirement_slot.val)

def authenticatedOutput (policy : GeneratedPolicy) (entry : GeneratedEntry)
    (registry : GeneratedRegistry) (currentSlot : Std.U64) :
    GeneratedAuthenticated where
  policy := policy
  pool := entry.pool
  verifierProgram := entry.verifier_program
  profileBinding := entry.profile_binding
  releaseBinding := entry.release_binding
  statementVersion := entry.statement_version
  registryGeneration := registry.generation
  authenticatedAtSlot := currentSlot

/-- Aeneas-compatible replacement for exactly the unsupported two-element
slice-pattern at `registry.rs:127`. Every subsequent operation is either a
transparent generated production decoder, a literal source check, or one of
the two named Solana boundaries above. -/
def correctedAuthenticate (runtime : SolanaBoundaries) (pool : Bytes32)
    (policy : GeneratedPolicy) (accounts : List AccountView)
    (selection : GeneratedSelection) (currentSlot : Std.U64) :
    Option GeneratedAuthenticated := do
  let [registryAccount, entryAccount] := accounts | none
  let _ ← decodedValue (pool_v1.format.validate_verifier_policy_v1 policy)
  let _ ← productionReadonlyResult registryAccount policy.registry_program
    .InvalidVerifierRegistry
  if hRegistryPda : registryAccount.key = registryPda runtime policy pool then
    pure ()
  else
    none
  let registryBytes ← runtime.tryBorrowData registryAccount
  let registry ← decodedValue
    (pool_v1.verifier_registry.decode_verifier_registry_v1 registryBytes)
  let immutableFlag ← resultValue
    pool_v1.format.POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY
  let immutableMask := policy.flags &&& immutableFlag
  let immutable ← resultValue
    (pool_v1.verifier_registry.VerifierRegistryV1.is_immutable registry)
  let paused ← resultValue
    (pool_v1.verifier_registry.VerifierRegistryV1.is_paused registry)
  if hRegistry : RegistryChecks pool policy registry
      (immutableMask != 0#u8) immutable paused then
    pure ()
  else
    none
  let _ ← productionReadonlyResult entryAccount policy.registry_program
    .InvalidVerifierEntry
  if hEntryPda : entryAccount.key = entryPda runtime policy pool selection then
    pure ()
  else
    none
  let entryBytes ← runtime.tryBorrowData entryAccount
  let entry ← decodedValue
    (pool_v1.verifier_registry.decode_verifier_registry_entry_v1 entryBytes)
  let noRetirement :=
    pool_v1.verifier_registry.POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT
  if hEntry : EntryChecks pool policy selection entry currentSlot noRetirement then
    some (authenticatedOutput policy entry registry currentSlot)
  else
    none

/-- Exact successful trace exposed by the corrected root. This inventory is
deliberately operational: it names decoder calls and boundary results, not the
authorization conclusion proved below. -/
def SuccessfulTrace (runtime : SolanaBoundaries) (pool : Bytes32)
    (policy : GeneratedPolicy) (accounts : List AccountView)
    (selection : GeneratedSelection) (currentSlot : Std.U64)
    (authenticated : GeneratedAuthenticated) : Prop :=
  ∃ registryAccount entryAccount registryBytes entryBytes registry entry
      immutableFlag immutableMask immutable paused noRetirement,
    accounts = [registryAccount, entryAccount] ∧
    decodedValue (pool_v1.format.validate_verifier_policy_v1 policy) = some () ∧
    productionReadonlyResult registryAccount policy.registry_program
      .InvalidVerifierRegistry = some () ∧
    registryAccount.key = registryPda runtime policy pool ∧
    runtime.tryBorrowData registryAccount = some registryBytes ∧
    decodedValue (pool_v1.verifier_registry.decode_verifier_registry_v1
      registryBytes) = some registry ∧
    resultValue pool_v1.format.POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY =
      some immutableFlag ∧
    immutableMask = policy.flags &&& immutableFlag ∧
    resultValue
      (pool_v1.verifier_registry.VerifierRegistryV1.is_immutable registry) =
      some immutable ∧
    resultValue
      (pool_v1.verifier_registry.VerifierRegistryV1.is_paused registry) =
      some paused ∧
    RegistryChecks pool policy registry (immutableMask != 0#u8) immutable paused ∧
    productionReadonlyResult entryAccount policy.registry_program
      .InvalidVerifierEntry = some () ∧
    entryAccount.key = entryPda runtime policy pool selection ∧
    runtime.tryBorrowData entryAccount = some entryBytes ∧
    decodedValue (pool_v1.verifier_registry.decode_verifier_registry_entry_v1
      entryBytes) = some entry ∧
    noRetirement =
      pool_v1.verifier_registry.POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT ∧
    EntryChecks pool policy selection entry currentSlot noRetirement ∧
    authenticated = authenticatedOutput policy entry registry currentSlot

theorem if_none_else_success {T : Type} {condition : Prop}
    [Decidable condition] {next : Option T} {value : T}
    (run : (if condition then next else none) = some value) :
    condition ∧ next = some value := by
  by_cases holds : condition
  · exact ⟨holds, by simpa [holds] using run⟩
  · simp [holds] at run

theorem corrected_success_implies_trace (runtime : SolanaBoundaries) (pool : Bytes32)
    (policy : GeneratedPolicy) (accounts : List AccountView)
    (selection : GeneratedSelection) (currentSlot : Std.U64)
    (authenticated : GeneratedAuthenticated)
    (run : correctedAuthenticate runtime pool policy accounts selection currentSlot =
      some authenticated) :
    SuccessfulTrace runtime pool policy accounts selection currentSlot authenticated := by
  cases accounts with
  | nil => simp [correctedAuthenticate] at run
  | cons registryAccount remaining =>
    cases remaining with
    | nil => simp [correctedAuthenticate] at run
    | cons entryAccount trailing =>
      cases trailing with
      | cons extra more => simp [correctedAuthenticate] at run
      | nil =>
        dsimp only [correctedAuthenticate] at run
        obtain ⟨policyUnit, policyValid, run⟩ :=
          Option.bind_eq_some_iff.mp run
        cases policyUnit
        obtain ⟨registryReadonlyUnit, registryReadonlySource, run⟩ :=
          Option.bind_eq_some_iff.mp run
        cases registryReadonlyUnit
        obtain ⟨registryAddress, run⟩ := if_none_else_success run
        obtain ⟨registryBytes, registryBorrow, run⟩ :=
          Option.bind_eq_some_iff.mp run
        obtain ⟨registry, registryDecode, run⟩ :=
          Option.bind_eq_some_iff.mp run
        obtain ⟨immutableFlag, immutableFlagExact, run⟩ :=
          Option.bind_eq_some_iff.mp run
        obtain ⟨immutable, immutableExact, run⟩ :=
          Option.bind_eq_some_iff.mp run
        obtain ⟨paused, pausedExact, run⟩ :=
          Option.bind_eq_some_iff.mp run
        obtain ⟨registryChecks, run⟩ := if_none_else_success run
        obtain ⟨entryReadonlyUnit, entryReadonlySource, run⟩ :=
          Option.bind_eq_some_iff.mp run
        cases entryReadonlyUnit
        obtain ⟨entryAddress, run⟩ := if_none_else_success run
        obtain ⟨entryBytes, entryBorrow, run⟩ :=
          Option.bind_eq_some_iff.mp run
        obtain ⟨entry, entryDecode, run⟩ :=
          Option.bind_eq_some_iff.mp run
        obtain ⟨entryChecks, run⟩ := if_none_else_success run
        have outputExact : authenticated =
            authenticatedOutput policy entry registry currentSlot :=
          (Option.some.inj run).symm
        exact ⟨registryAccount, entryAccount, registryBytes, entryBytes,
          registry, entry, immutableFlag, policy.flags &&& immutableFlag,
          immutable, paused,
          pool_v1.verifier_registry.POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
          rfl, policyValid, registryReadonlySource, registryAddress, registryBorrow,
          registryDecode, immutableFlagExact, rfl, immutableExact, pausedExact,
          registryChecks, entryReadonlySource, entryAddress, entryBorrow, entryDecode,
          rfl, entryChecks, outputExact⟩

def bytesNat (bytes : Bytes32) : Nat :=
  bytes.val.foldl (fun accumulator byte => accumulator * 256 + byte.val) 0

def policyOfGenerated (policy : GeneratedPolicy)
    (policyRequiresImmutable : Bool) : Policy where
  registryProgram := bytesNat policy.registry_program
  registryAuthority := bytesNat policy.registry_authority
  policyBinding := bytesNat policy.policy_binding
  immutable := policyRequiresImmutable

def registryOfGenerated (policy : GeneratedPolicy) (registry : GeneratedRegistry)
    (immutable paused : Bool) : Registry where
  pool := bytesNat registry.pool
  registryProgram := bytesNat policy.registry_program
  authority := bytesNat registry.authority
  policyBinding := bytesNat registry.policy_binding
  immutable := immutable
  paused := paused
  generation := registry.generation.val
  minimumActivationDelaySlots := registry.minimum_activation_delay_slots.val

def statusOfGenerated :
    pool_v1.verifier_registry.VerifierEntryStatusV1 → EntryStatus
  | .Pending => .pending
  | .Active => .active
  | .Paused => .paused
  | .Retired => .retired

def entryOfGenerated (entry : GeneratedEntry) (noRetirement : Std.U64) : Entry where
  pool := bytesNat entry.pool
  verifierProgram := bytesNat entry.verifier_program
  profileBinding := bytesNat entry.profile_binding
  releaseBinding := bytesNat entry.release_binding
  statementVersion := entry.statement_version.val
  activationSlot := entry.activation_slot.val
  retirementSlot :=
    if entry.retirement_slot = noRetirement then none
    else some entry.retirement_slot.val
  policyBinding := bytesNat entry.policy_binding
  status := statusOfGenerated entry.status

def selectionOfGenerated (selection : GeneratedSelection) : Selection where
  verifierProgram := bytesNat selection.verifierProgram
  profileBinding := bytesNat selection.profileBinding
  releaseBinding := bytesNat selection.releaseBinding
  statementVersion := selection.statementVersion.val

def BindingMatchesGenerated
    (pool : Bytes32) (selection : GeneratedSelection)
    (binding : AspisPool.AuthorizationReceiptV1.Binding) : Prop :=
  binding.pool = bytesNat pool ∧
    binding.verifierProgram = bytesNat selection.verifierProgram ∧
    binding.profileBinding = bytesNat selection.profileBinding ∧
    binding.releaseBinding = bytesNat selection.releaseBinding ∧
    binding.statementVersion = selection.statementVersion.val

theorem binding_matches_generated_exact_selection
    (pool : Bytes32) (selection : GeneratedSelection)
    (binding : AspisPool.AuthorizationReceiptV1.Binding)
    (bindingMatches : BindingMatchesGenerated pool selection binding) :
    binding.pool = bytesNat pool ∧
      binding.selection = selectionOfGenerated selection := by
  rcases bindingMatches with ⟨poolExact, verifier, profile, release, statement⟩
  refine ⟨poolExact, ?_⟩
  cases binding
  simp_all [AspisPool.AuthorizationReceiptV1.Binding.selection,
    selectionOfGenerated]

def OutputExact (authenticated : GeneratedAuthenticated)
    (policy : GeneratedPolicy) (registry : GeneratedRegistry)
    (entry : GeneratedEntry) (currentSlot : Std.U64) : Prop :=
  authenticated = authenticatedOutput policy entry registry currentSlot

def AccountPins (runtime : SolanaBoundaries) (pool : Bytes32)
    (policy : GeneratedPolicy) (selection : GeneratedSelection)
    (registryAccount entryAccount : AccountView) : Prop :=
  ReadonlyOwned registryAccount policy.registry_program ∧
    registryAccount.key = registryPda runtime policy pool ∧
    ReadonlyOwned entryAccount policy.registry_program ∧
    entryAccount.key = entryPda runtime policy pool selection

theorem decoded_checks_imply_formal_authorized (pool : Bytes32)
    (policy : GeneratedPolicy) (registry : GeneratedRegistry)
    (entry : GeneratedEntry) (selection : GeneratedSelection)
    (currentSlot noRetirement : Std.U64)
    (immutableMask : Std.U8) (immutable paused : Bool)
    (registryChecks : RegistryChecks pool policy registry
      (immutableMask != 0#u8) immutable paused)
    (entryChecks : EntryChecks pool policy selection entry currentSlot noRetirement) :
    Authorized (bytesNat pool)
      (policyOfGenerated policy (immutableMask != 0#u8))
      (registryOfGenerated policy registry immutable paused)
      (entryOfGenerated entry noRetirement)
      (selectionOfGenerated selection) currentSlot.val := by
  rcases registryChecks with
    ⟨registryPool, registryAuthority, registryPolicy, immutableExact, notPaused⟩
  rcases entryChecks with
    ⟨entryPool, entryPolicy, verifier, profile, release, statement, active,
      activation, retirement⟩
  simp only [Authorized, policyOfGenerated, registryOfGenerated,
    entryOfGenerated, selectionOfGenerated, ActiveAt]
  constructor
  · simpa [registryPool]
  constructor
  · trivial
  constructor
  · simpa [registryAuthority]
  constructor
  · simpa [registryPolicy]
  constructor
  · exact immutableExact
  constructor
  · exact notPaused
  constructor
  · simpa [entryPool]
  constructor
  · simpa [entryPolicy]
  constructor
  · simpa [verifier]
  constructor
  · simpa [profile]
  constructor
  · simpa [release]
  constructor
  · simpa [statement]
  constructor
  · simpa [active, statusOfGenerated]
  constructor
  · exact activation
  intro retirementSlot retirementExact
  by_cases noSlot : entry.retirement_slot = noRetirement
  · simp [noSlot] at retirementExact
  · simp [noSlot] at retirementExact
    rcases retirement with same | before
    · exact False.elim (noSlot same)
    · simpa [← retirementExact] using before

theorem corrected_production_success_implies_exact_authorization
    (runtime : SolanaBoundaries) (pool : Bytes32)
    (policy : GeneratedPolicy) (accounts : List AccountView)
    (selection : GeneratedSelection) (currentSlot : Std.U64)
    (authenticated : GeneratedAuthenticated)
    (run : correctedAuthenticate runtime pool policy accounts selection currentSlot =
      some authenticated) :
    ∃ registryAccount entryAccount registry entry immutableMask immutable paused
        noRetirement,
      SuccessfulTrace runtime pool policy accounts selection currentSlot authenticated ∧
      accounts = [registryAccount, entryAccount] ∧
      AccountPins runtime pool policy selection registryAccount entryAccount ∧
      OutputExact authenticated policy registry entry currentSlot ∧
      Authorized (bytesNat pool)
        (policyOfGenerated policy (immutableMask != 0#u8))
        (registryOfGenerated policy registry immutable paused)
        (entryOfGenerated entry noRetirement)
        (selectionOfGenerated selection) currentSlot.val := by
  have trace := corrected_success_implies_trace runtime pool policy accounts selection
    currentSlot authenticated run
  have sourceTrace := trace
  rcases trace with
    ⟨registryAccount, entryAccount, registryBytes, entryBytes, registry, entry,
      immutableFlag, immutableMask, immutable, paused, noRetirement, accountsExact,
      policyValid, registryReadonlySource, registryAddress, registryBorrow,
      registryDecode,
      immutableFlagExact, immutableMaskExact, immutableExact, pausedExact,
      registryChecks, entryReadonlySource, entryAddress, entryBorrow, entryDecode,
      noRetirementExact, entryChecks, outputExact⟩
  have registryReadonly :=
    (production_readonly_success_iff registryAccount policy.registry_program
      .InvalidVerifierRegistry).mp registryReadonlySource
  have entryReadonly :=
    (production_readonly_success_iff entryAccount policy.registry_program
      .InvalidVerifierEntry).mp entryReadonlySource
  refine ⟨registryAccount, entryAccount, registry, entry, immutableMask, immutable,
    paused, noRetirement, sourceTrace, accountsExact, ?_, outputExact, ?_⟩
  · exact ⟨registryReadonly, registryAddress, entryReadonly, entryAddress⟩
  · exact decoded_checks_imply_formal_authorized pool policy registry entry selection
      currentSlot noRetirement immutableMask immutable paused registryChecks entryChecks

theorem corrected_production_success_implies_receipt_registry_authorization
    (runtime : SolanaBoundaries) (pool : Bytes32)
    (policy : GeneratedPolicy) (accounts : List AccountView)
    (selection : GeneratedSelection) (currentSlot : Std.U64)
    (authenticated : GeneratedAuthenticated)
    (binding : AspisPool.AuthorizationReceiptV1.Binding)
    (bindingMatches : BindingMatchesGenerated pool selection binding)
    (run : correctedAuthenticate runtime pool policy accounts selection currentSlot =
      some authenticated) :
    ∃ registryAccount entryAccount registry entry immutableMask immutable paused
        noRetirement,
      SuccessfulTrace runtime pool policy accounts selection currentSlot authenticated ∧
      accounts = [registryAccount, entryAccount] ∧
      AccountPins runtime pool policy selection registryAccount entryAccount ∧
      OutputExact authenticated policy registry entry currentSlot ∧
      Authorized binding.pool
        (policyOfGenerated policy (immutableMask != 0#u8))
        (registryOfGenerated policy registry immutable paused)
        (entryOfGenerated entry noRetirement)
        binding.selection currentSlot.val := by
  rcases corrected_production_success_implies_exact_authorization runtime pool policy
      accounts selection currentSlot authenticated run with
    ⟨registryAccount, entryAccount, registry, entry, immutableMask, immutable,
      paused, noRetirement, sourceTrace, accountsExact, pins, outputExact, authorized⟩
  obtain ⟨poolExact, selectionExact⟩ :=
    binding_matches_generated_exact_selection pool selection binding bindingMatches
  refine ⟨registryAccount, entryAccount, registry, entry, immutableMask, immutable,
    paused, noRetirement, sourceTrace, accountsExact, pins, outputExact, ?_⟩
  rw [poolExact, selectionExact]
  exact authorized

#print axioms corrected_success_implies_trace
#print axioms decoded_checks_imply_formal_authorized
#print axioms corrected_production_success_implies_exact_authorization
#print axioms corrected_production_success_implies_receipt_registry_authorization

end

end AspisPool.VerifierRegistrySourceBridge
