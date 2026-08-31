import V7RegistryV2ProductionCodecs.Funs
import V7RegistryV2ProductionReadonly.Funs
import V7RegistryV2OneTerminalCaller.Types

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisPool.V7RegistryV2AccountInfoProjectionBridge

noncomputable section

local instance {T : Type} : DecidableEq T := Classical.decEq T
local instance {proposition : Prop} : Decidable proposition :=
  Classical.propDecidable proposition

abbrev Bytes32 := Array Std.U8 32#usize
abbrev RegistryV2 :=
  V7RegistryV2ProductionCodecsGenerated.pool_v1.verifier_registry.VerifierRegistryV2
abbrev EntryV2 :=
  V7RegistryV2ProductionCodecsGenerated.pool_v1.verifier_registry.VerifierRegistryEntryV2
abbrev SourceAccount :=
  V7RegistryV2ProductionReadonlyGenerated.solana_account_info.AccountInfo
abbrev SourcePubkey := solana_pubkey.Pubkey
abbrev FixedAccountView := V7RegistryV2OneTerminalCallerGenerated.AccountView

def zero32 : Bytes32 := Array.repeat 32#usize 0#u8

def decodedValue {T E : Type} : Result (core.result.Result T E) → Option T
  | .ok (.Ok value) => some value
  | _ => none

def sourceReadonlyAccepted (account : SourceAccount) (owner : SourcePubkey)
    (invalid : V7RegistryV2ProductionReadonlyGenerated.error.PoolV1ProgramError) : Prop :=
  V7RegistryV2ProductionReadonlyGenerated.registry.require_readonly_registry_account
      account owner invalid =
    .ok (.Ok ())

def ReadonlyOwned (account : SourceAccount) (owner : SourcePubkey) : Prop :=
  account.owner = owner ∧
    account.executable = false ∧
    account.is_writable = false ∧
    account.is_signer = false

theorem production_readonly_success_iff
    (account : SourceAccount) (owner : SourcePubkey)
    (invalid : V7RegistryV2ProductionReadonlyGenerated.error.PoolV1ProgramError) :
    sourceReadonlyAccepted account owner invalid ↔ ReadonlyOwned account owner := by
  have ownerValExact : account.owner.val = owner.val ↔ account.owner = owner := by
    constructor
    · exact fun equal => Subtype.ext equal
    · intro equal
      cases equal
      rfl
  by_cases ownerExact : account.owner = owner
  all_goals cases executableExact : account.executable
  all_goals cases writableExact : account.is_writable
  all_goals cases signerExact : account.is_signer
  all_goals simp [sourceReadonlyAccepted, ReadonlyOwned,
    V7RegistryV2ProductionReadonlyGenerated.registry.require_readonly_registry_account,
    solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq,
    V7RegistryV2ProductionReadonlyGenerated.solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from,
    core.cmp.impls.PartialEqShared.ne, core.cmp.PartialEq.ne.default,
    core.convert.IntoFrom.into, ownerExact, executableExact, writableExact,
    signerExact, ownerValExact]

/-!
## Honest finite fixed-width projection

The operational caller represents public identities by `u64`; production
`AccountInfo` uses 32-byte public keys.  There is no injective map from all
32-byte strings to `u64`, so the bridge deliberately asks only for equality
reflection on the finite owner/key pairs used by this transaction.
-/

structure FixedWidthProjection where
  encode : SourcePubkey → Std.U64

def FixedWidthProjection.ReflectsPair (projection : FixedWidthProjection)
    (left right : SourcePubkey) : Prop :=
  projection.encode left = projection.encode right ↔ left = right

def projectAccountView (projection : FixedWidthProjection)
    (account : SourceAccount) : FixedAccountView := {
  key := projection.encode account.key
  owner := projection.encode account.owner
  writable := account.is_writable
  signer := account.is_signer
  executable := account.executable
}

def FixedReadonlyOwned (account : FixedAccountView) (owner : Std.U64) : Prop :=
  account.owner = owner ∧
    account.executable = false ∧
    account.writable = false ∧
    account.signer = false

theorem production_readonly_success_iff_projected_account
    (projection : FixedWidthProjection)
    (account : SourceAccount) (owner : SourcePubkey)
    (invalid : V7RegistryV2ProductionReadonlyGenerated.error.PoolV1ProgramError)
    (ownerExact : projection.ReflectsPair account.owner owner) :
    sourceReadonlyAccepted account owner invalid ↔
      FixedReadonlyOwned (projectAccountView projection account)
        (projection.encode owner) := by
  rw [production_readonly_success_iff]
  constructor
  · rintro ⟨ownerEqual, executable, writable, signer⟩
    exact ⟨congrArg projection.encode ownerEqual, executable, writable, signer⟩
  · rintro ⟨ownerEqual, executable, writable, signer⟩
    exact ⟨ownerExact.mp ownerEqual, executable, writable, signer⟩

def productionRegistryAccountsAccepted
    (registry entry : SourceAccount) (registryProgram : SourcePubkey)
    (registryInvalid entryInvalid :
      V7RegistryV2ProductionReadonlyGenerated.error.PoolV1ProgramError) : Prop :=
  sourceReadonlyAccepted registry registryProgram registryInvalid ∧
    sourceReadonlyAccepted entry registryProgram entryInvalid

def FixedRegistryAccountFields
    (registry entry : FixedAccountView) (registryProgram : Std.U64) : Prop :=
  registry.owner = registryProgram ∧
    entry.owner = registryProgram ∧
    registry.writable = false ∧
    registry.signer = false ∧
    entry.writable = false ∧
    entry.signer = false

def FixedRegistryAccountSourceShape
    (registry entry : FixedAccountView) (registryProgram : Std.U64) : Prop :=
  FixedRegistryAccountFields registry entry registryProgram ∧
    registry.executable = false ∧
    entry.executable = false

theorem production_registry_pair_iff_fixed_source_shape
    (projection : FixedWidthProjection)
    (registry entry : SourceAccount) (registryProgram : SourcePubkey)
    (registryInvalid entryInvalid :
      V7RegistryV2ProductionReadonlyGenerated.error.PoolV1ProgramError)
    (registryOwnerExact :
      projection.ReflectsPair registry.owner registryProgram)
    (entryOwnerExact :
      projection.ReflectsPair entry.owner registryProgram) :
    productionRegistryAccountsAccepted registry entry registryProgram
        registryInvalid entryInvalid ↔
      FixedRegistryAccountSourceShape
        (projectAccountView projection registry)
        (projectAccountView projection entry)
        (projection.encode registryProgram) := by
  unfold productionRegistryAccountsAccepted
  rw [production_readonly_success_iff_projected_account projection registry
      registryProgram registryInvalid registryOwnerExact,
    production_readonly_success_iff_projected_account projection entry
      registryProgram entryInvalid entryOwnerExact]
  simp only [productionRegistryAccountsAccepted, FixedRegistryAccountSourceShape,
    FixedRegistryAccountFields, FixedReadonlyOwned, projectAccountView]
  aesop

theorem production_registry_pair_supplies_fixed_account_fields
    (projection : FixedWidthProjection)
    (registry entry : SourceAccount) (registryProgram : SourcePubkey)
    (registryInvalid entryInvalid :
      V7RegistryV2ProductionReadonlyGenerated.error.PoolV1ProgramError)
    (registryOwnerExact :
      projection.ReflectsPair registry.owner registryProgram)
    (entryOwnerExact :
      projection.ReflectsPair entry.owner registryProgram)
    (accepted : productionRegistryAccountsAccepted registry entry
      registryProgram registryInvalid entryInvalid) :
    FixedRegistryAccountFields
      (projectAccountView projection registry)
      (projectAccountView projection entry)
      (projection.encode registryProgram) := by
  have sourceShape :=
    (production_registry_pair_iff_fixed_source_shape projection registry entry
      registryProgram registryInvalid entryInvalid registryOwnerExact
      entryOwnerExact).mp accepted
  exact sourceShape.1

def RegistryValidationFacts (registry : RegistryV2) : Prop :=
  registry.pool ≠ zero32 ∧
    registry.policy_binding ≠ zero32 ∧
    registry.registry_program ≠ zero32 ∧
    registry.loader_program ≠ zero32 ∧
    registry.programdata_address ≠ zero32 ∧
    registry.executable_hash ≠ zero32 ∧
    registry.authority = zero32 ∧
    registry.minimum_activation_delay_slots ≠ 0#u64

def EntryValidationFacts (entry : EntryV2) : Prop :=
  entry.statement_version ≠ 0#u8 ∧
    entry.pool ≠ zero32 ∧
    entry.verifier_program ≠ zero32 ∧
    entry.profile_binding ≠ zero32 ∧
    entry.release_binding ≠ zero32 ∧
    entry.loader_program ≠ zero32 ∧
    entry.programdata_address ≠ zero32 ∧
    entry.executable_hash ≠ zero32 ∧
    entry.policy_binding ≠ zero32 ∧
    entry.expected_upgrade_authority = zero32 ∧
    (entry.retirement_slot =
        V7RegistryV2ProductionCodecsGenerated.pool_v1.verifier_registry.POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT ∨
      entry.activation_slot.val < entry.retirement_slot.val)

private theorem list_allM_u8_eq_true_implies_equal :
    ∀ (left right : List Std.U8),
      List.allM
          (fun pair : Std.U8 × Std.U8 =>
            Result.ok (decide (pair.1.val = pair.2.val)))
          (List.zip left right) = Result.ok true →
        left.length = right.length → left = right := by
  intro left
  induction left with
  | nil =>
      intro right allEqual sameLength
      cases right <;> simp_all
  | cons leftHead leftTail inductionHypothesis =>
      intro right allEqual sameLength
      cases right with
      | nil => simp at sameLength
      | cons rightHead rightTail =>
          by_cases headValuesEqual : leftHead.val = rightHead.val
          · simp [List.allM, headValuesEqual] at allEqual
            have headEqual : leftHead = rightHead :=
              UScalar.eq_of_val_eq headValuesEqual
            subst rightHead
            have tailLength : leftTail.length = rightTail.length := by
              simpa using sameLength
            exact congrArg (List.cons leftHead)
              (inductionHypothesis rightTail allEqual tailLength)
          · simp [List.allM, headValuesEqual, pure] at allEqual

private theorem list_allM_u8_is_ok :
    ∀ (pairs : List (Std.U8 × Std.U8)), ∃ result : Bool,
      List.allM
          (fun pair : Std.U8 × Std.U8 =>
            Result.ok (decide (pair.1.val = pair.2.val))) pairs =
        Result.ok result := by
  intro pairs
  induction pairs with
  | nil => exact ⟨true, rfl⟩
  | cons pair tail inductionHypothesis =>
      rcases inductionHypothesis with ⟨tailResult, tailRun⟩
      by_cases equal : pair.1.val = pair.2.val
      · exact ⟨tailResult, by simp [List.allM, equal, tailRun, pure]⟩
      · exact ⟨false, by simp [List.allM, equal, pure]⟩

private theorem list_allM_u8_self_is_true :
    ∀ (values : List Std.U8),
      List.allM
          (fun pair : Std.U8 × Std.U8 =>
            Result.ok (decide (pair.1.val = pair.2.val)))
          (List.zip values values) = Result.ok true := by
  intro values
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [List.allM, inductionHypothesis]

theorem partial_eq_u8_array_true_implies_equal
    {length : Std.Usize} (left right : Array Std.U8 length)
    (run : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      left right = .ok true) : left = right := by
  unfold core.array.equality.PartialEqArray.eq at run
  simp [core.cmp.PartialEqU8, core.cmp.impls.PartialEqU8.ne,
    Aeneas.Std.liftFun2] at run
  apply Subtype.ext
  exact list_allM_u8_eq_true_implies_equal left.val right.val run
    (by simpa using left.property.trans right.property.symm)

theorem partial_eq_u8_array_refl
    {length : Std.Usize} (value : Array Std.U8 length) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 value value =
      .ok true := by
  unfold core.array.equality.PartialEqArray.eq
  simp only [Array.length, ↓reduceIte]
  simpa [core.cmp.PartialEqU8, core.cmp.impls.PartialEqU8.ne,
    Aeneas.Std.liftFun2] using list_allM_u8_self_is_true value.val

theorem partial_eq_u8_array_is_ok
    {length : Std.Usize} (left right : Array Std.U8 length) :
    ∃ result : Bool,
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 left right =
        .ok result := by
  unfold core.array.equality.PartialEqArray.eq
  simp only [Array.length, ↓reduceIte]
  simpa [core.cmp.PartialEqU8, core.cmp.impls.PartialEqU8.ne,
    Aeneas.Std.liftFun2] using list_allM_u8_is_ok (List.zip left.val right.val)

theorem partial_eq_u8_array_true_iff
    {length : Std.Usize} (left right : Array Std.U8 length) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 left right =
      .ok true ↔ left = right := by
  constructor
  · exact partial_eq_u8_array_true_implies_equal left right
  · intro equal
    subst right
    exact partial_eq_u8_array_refl left

theorem partial_eq_u8_array_false_iff
    {length : Std.Usize} (left right : Array Std.U8 length) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 left right =
      .ok false ↔ left ≠ right := by
  constructor
  · intro run equal
    subst right
    rw [partial_eq_u8_array_refl left] at run
    cases run
  · intro different
    rcases partial_eq_u8_array_is_ok left right with ⟨result, run⟩
    cases result
    · exact run
    · exact False.elim
        (different (partial_eq_u8_array_true_implies_equal left right run))

theorem required_binding_is_zero_ok_iff (value : Bytes32) :
    V7RegistryV2ProductionCodecsGenerated.pool_v1.verifier_registry.required_binding_is_zero
        value = .ok true ↔
      value = zero32 := by
  exact partial_eq_u8_array_true_iff value zero32

theorem required_binding_is_nonzero_ok_iff (value : Bytes32) :
    V7RegistryV2ProductionCodecsGenerated.pool_v1.verifier_registry.required_binding_is_zero
        value = .ok false ↔
      value ≠ zero32 := by
  exact partial_eq_u8_array_false_iff value zero32

#print axioms production_readonly_success_iff
#print axioms production_readonly_success_iff_projected_account
#print axioms production_registry_pair_iff_fixed_source_shape
#print axioms production_registry_pair_supplies_fixed_account_fields
#print axioms required_binding_is_zero_ok_iff
#print axioms required_binding_is_nonzero_ok_iff

end

end AspisPool.V7RegistryV2AccountInfoProjectionBridge
