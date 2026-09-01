import V7RegistryV2DeploymentCertificate.Funs
import V7RegistryV2AccountInfoProjectionBridge
import V7RegistryV2OneTerminalCallerSourceBridge

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7RegistryV2DeploymentCertificateGenerated

noncomputable section

local instance {T : Type} : DecidableEq T := Classical.decEq T
local instance {proposition : Prop} : Decidable proposition :=
  Classical.propDecidable proposition

abbrev Bytes32 := Array Std.U8 32#usize

def zero32 : Bytes32 := Array.repeat 32#usize 0#u8

theorem partial_ne_u8_array_exact (left right : Bytes32) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 left right =
      .ok (decide (left ≠ right)) := by
  unfold core.array.equality.PartialEqArray.ne
  by_cases equal : left = right
  · subst right
    rw [AspisPool.V7RegistryV2AccountInfoProjectionBridge.partial_eq_u8_array_refl]
    simp
  · rw [(AspisPool.V7RegistryV2AccountInfoProjectionBridge.partial_eq_u8_array_false_iff
      left right).2 equal]
    simp [equal]

theorem partial_eq_u8_array_exact (left right : Bytes32) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 left right =
      .ok (decide (left = right)) := by
  by_cases equal : left = right
  · subst right
    rw [AspisPool.V7RegistryV2AccountInfoProjectionBridge.partial_eq_u8_array_refl]
    simp
  · rw [(AspisPool.V7RegistryV2AccountInfoProjectionBridge.partial_eq_u8_array_false_iff
      left right).2 equal]
    simp [equal]

def ExactImmutableDeploymentSuccess
    (observation : DeploymentObservation)
    (certificate : ImmutableDeploymentCertificate) : Prop :=
  observation.program_account.key = observation.expected_program ∧
  observation.program_account.owner = observation.loader_v3 ∧
  observation.program_account.executable = true ∧
  observation.program_account.signer = false ∧
  observation.program_account.writable = false ∧
  observation.programdata_account.owner = observation.loader_v3 ∧
  observation.programdata_account.executable = false ∧
  observation.programdata_account.signer = false ∧
  observation.programdata_account.writable = false ∧
  observation.program_account_data_len = LOADER_V3_PROGRAM_BYTES ∧
  observation.program_decode =
    .Program observation.programdata_account.key ∧
  observation.programdata_account.key = observation.derived_programdata ∧
  ¬ observation.programdata_account_data_len ≤
    LOADER_V3_PROGRAMDATA_METADATA_BYTES ∧
  observation.programdata_decode = .Immutable ∧
  observation.executable_sha256 ≠ zero32 ∧
  certificate = {
    program := observation.expected_program
    loader_v3 := observation.loader_v3
    programdata_address := observation.programdata_account.key
    executable_sha256 := observation.executable_sha256
  }

theorem translated_immutable_deployment_success_is_exact
    (observation : DeploymentObservation)
    (certificate : ImmutableDeploymentCertificate)
    (run : authenticate_immutable_loader_v3_deployment_projection observation =
      .ok (.Ok certificate)) :
    ExactImmutableDeploymentSuccess observation certificate := by
  have programKey :
      observation.program_account.key = observation.expected_program := by
    by_contra different
    simp [authenticate_immutable_loader_v3_deployment_projection,
      partial_ne_u8_array_exact, different] at run
  have programOwner :
      observation.program_account.owner = observation.loader_v3 := by
    by_contra different
    simp [authenticate_immutable_loader_v3_deployment_projection,
      partial_ne_u8_array_exact, programKey, different] at run
  have programExecutable : observation.program_account.executable = true := by
    cases executable : observation.program_account.executable with
    | false =>
        simp [authenticate_immutable_loader_v3_deployment_projection,
          partial_ne_u8_array_exact, programKey, programOwner, executable] at run
    | true => rfl
  have programNonsigner : observation.program_account.signer = false := by
    cases signer : observation.program_account.signer with
    | false => rfl
    | true =>
        simp [authenticate_immutable_loader_v3_deployment_projection,
          partial_ne_u8_array_exact, programKey, programOwner,
          programExecutable, signer] at run
  have programReadonly : observation.program_account.writable = false := by
    cases writable : observation.program_account.writable with
    | false => rfl
    | true =>
        simp [authenticate_immutable_loader_v3_deployment_projection,
          partial_ne_u8_array_exact, programKey, programOwner,
          programExecutable, programNonsigner, writable] at run
  have programdataOwner :
      observation.programdata_account.owner = observation.loader_v3 := by
    by_contra different
    simp [authenticate_immutable_loader_v3_deployment_projection,
      partial_ne_u8_array_exact, programKey, programOwner,
      programExecutable, programNonsigner, programReadonly, different] at run
  have programdataNonexecutable :
      observation.programdata_account.executable = false := by
    cases executable : observation.programdata_account.executable with
    | false => rfl
    | true =>
        simp [authenticate_immutable_loader_v3_deployment_projection,
          partial_ne_u8_array_exact, programKey, programOwner,
          programExecutable, programNonsigner, programReadonly,
          programdataOwner, executable] at run
  have programdataNonsigner :
      observation.programdata_account.signer = false := by
    cases signer : observation.programdata_account.signer with
    | false => rfl
    | true =>
        simp [authenticate_immutable_loader_v3_deployment_projection,
          partial_ne_u8_array_exact, programKey, programOwner,
          programExecutable, programNonsigner, programReadonly,
          programdataOwner, programdataNonexecutable, signer] at run
  have programdataReadonly :
      observation.programdata_account.writable = false := by
    cases writable : observation.programdata_account.writable with
    | false => rfl
    | true =>
        simp [authenticate_immutable_loader_v3_deployment_projection,
          partial_ne_u8_array_exact, programKey, programOwner,
          programExecutable, programNonsigner, programReadonly,
          programdataOwner, programdataNonexecutable,
          programdataNonsigner, writable] at run
  have programLength :
      observation.program_account_data_len = LOADER_V3_PROGRAM_BYTES := by
    by_contra different
    simp [authenticate_immutable_loader_v3_deployment_projection,
      partial_ne_u8_array_exact, programKey, programOwner,
      programExecutable, programNonsigner, programReadonly,
      programdataOwner, programdataNonexecutable, programdataNonsigner,
      programdataReadonly, different] at run
  cases programDecode : observation.program_decode with
  | DecodeError =>
      simp [authenticate_immutable_loader_v3_deployment_projection,
        partial_ne_u8_array_exact, programKey, programOwner,
        programExecutable, programNonsigner, programReadonly,
        programdataOwner, programdataNonexecutable, programdataNonsigner,
        programdataReadonly, programLength, programDecode] at run
  | OtherVariant =>
      simp [authenticate_immutable_loader_v3_deployment_projection,
        partial_ne_u8_array_exact, programKey, programOwner,
        programExecutable, programNonsigner, programReadonly,
        programdataOwner, programdataNonexecutable, programdataNonsigner,
        programdataReadonly, programLength, programDecode] at run
  | Program linkedProgramdata =>
      have linkedAccount :
          linkedProgramdata = observation.programdata_account.key := by
        by_contra different
        simp [authenticate_immutable_loader_v3_deployment_projection,
          partial_ne_u8_array_exact, programKey, programOwner,
          programExecutable, programNonsigner, programReadonly,
          programdataOwner, programdataNonexecutable, programdataNonsigner,
          programdataReadonly, programLength, programDecode, different] at run
      have linkedDerived :
          linkedProgramdata = observation.derived_programdata := by
        by_contra different
        have accountDifferent :
            observation.programdata_account.key ≠
              observation.derived_programdata := by
          intro equal
          exact different (linkedAccount.trans equal)
        simp [authenticate_immutable_loader_v3_deployment_projection,
          partial_ne_u8_array_exact, programKey, programOwner,
          programExecutable, programNonsigner, programReadonly,
          programdataOwner, programdataNonexecutable, programdataNonsigner,
          programdataReadonly, programLength, programDecode, linkedAccount,
          accountDifferent] at run
      have accountDerived :
          observation.programdata_account.key =
            observation.derived_programdata :=
        linkedAccount.symm.trans linkedDerived
      have payloadExists :
          ¬ observation.programdata_account_data_len ≤
            LOADER_V3_PROGRAMDATA_METADATA_BYTES := by
        intro tooShort
        simp [authenticate_immutable_loader_v3_deployment_projection,
          partial_ne_u8_array_exact, programKey, programOwner,
          programExecutable, programNonsigner, programReadonly,
          programdataOwner, programdataNonexecutable, programdataNonsigner,
          programdataReadonly, programLength, programDecode, linkedAccount,
          accountDerived, tooShort] at run
      cases programdataDecode : observation.programdata_decode with
      | DecodeError =>
          simp [authenticate_immutable_loader_v3_deployment_projection,
            partial_ne_u8_array_exact, programKey, programOwner,
            programExecutable, programNonsigner, programReadonly,
            programdataOwner, programdataNonexecutable, programdataNonsigner,
            programdataReadonly, programLength, programDecode, linkedAccount,
            accountDerived, payloadExists, programdataDecode] at run
      | Mutable =>
          simp [authenticate_immutable_loader_v3_deployment_projection,
            partial_ne_u8_array_exact, programKey, programOwner,
            programExecutable, programNonsigner, programReadonly,
            programdataOwner, programdataNonexecutable, programdataNonsigner,
            programdataReadonly, programLength, programDecode, linkedAccount,
            accountDerived, payloadExists, programdataDecode] at run
      | OtherVariant =>
          simp [authenticate_immutable_loader_v3_deployment_projection,
            partial_ne_u8_array_exact, programKey, programOwner,
            programExecutable, programNonsigner, programReadonly,
            programdataOwner, programdataNonexecutable, programdataNonsigner,
            programdataReadonly, programLength, programDecode, linkedAccount,
            accountDerived, payloadExists, programdataDecode] at run
      | Immutable =>
          have hashNonzero : observation.executable_sha256 ≠ zero32 := by
            intro zeroHash
            simp [authenticate_immutable_loader_v3_deployment_projection,
              partial_ne_u8_array_exact, partial_eq_u8_array_exact,
              programKey, programOwner, programExecutable, programNonsigner,
              programReadonly, programdataOwner, programdataNonexecutable,
              programdataNonsigner, programdataReadonly, programLength,
              programDecode, linkedAccount, accountDerived, payloadExists,
              programdataDecode, zero32, zeroHash] at run
          have hashNotRepeat :
              observation.executable_sha256 ≠ Array.repeat 32#usize 0#u8 := by
            simpa [zero32] using hashNonzero
          have certificateForward :
              ({
                program := observation.expected_program
                loader_v3 := observation.loader_v3
                programdata_address := linkedProgramdata
                executable_sha256 := observation.executable_sha256
              } : ImmutableDeploymentCertificate) = certificate := by
            simpa [authenticate_immutable_loader_v3_deployment_projection,
              partial_ne_u8_array_exact, partial_eq_u8_array_exact,
              programKey, programOwner, programExecutable, programNonsigner,
              programReadonly, programdataOwner, programdataNonexecutable,
              programdataNonsigner, programdataReadonly, programLength,
              programDecode, linkedAccount, accountDerived, payloadExists,
              programdataDecode, hashNotRepeat] using run
          refine ⟨programKey, programOwner, programExecutable,
            programNonsigner, programReadonly, programdataOwner,
            programdataNonexecutable, programdataNonsigner,
            programdataReadonly, programLength, ?_, ?_, payloadExists,
            programdataDecode, hashNonzero, ?_⟩
          · simpa [linkedAccount] using programDecode
          · exact accountDerived
          · simpa [linkedAccount] using certificateForward.symm

def ExactDeploymentSourceRootSuccess
    (observation : DeploymentObservation)
    (expectedExecutableSha256 : Bytes32)
    (certificate : ImmutableDeploymentCertificate) : Prop :=
  ExactImmutableDeploymentSuccess observation certificate ∧
    observation.executable_sha256 = expectedExecutableSha256

theorem ExactImmutableDeploymentSuccess.certificate_executable_sha256
    {observation : DeploymentObservation}
    {certificate : ImmutableDeploymentCertificate}
    (exact : ExactImmutableDeploymentSuccess observation certificate) :
    certificate.executable_sha256 = observation.executable_sha256 := by
  rcases exact with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, certificateExact⟩
  rw [certificateExact]

theorem translated_deployment_source_root_success_is_exact
    (observation : DeploymentObservation)
    (expectedExecutableSha256 : Bytes32)
    (certificate : ImmutableDeploymentCertificate)
    (run : deployment_certificate_source_roots observation
      expectedExecutableSha256 = .ok (.Ok certificate)) :
    ExactDeploymentSourceRootSuccess observation expectedExecutableSha256
      certificate := by
  unfold deployment_certificate_source_roots at run
  cases authenticationRun :
      authenticate_immutable_loader_v3_deployment_projection observation with
  | fail error => simp [authenticationRun] at run
  | div => simp [authenticationRun] at run
  | ok authenticationResult =>
      cases authenticationResult with
      | Err error =>
          simp [authenticationRun,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at run
      | Ok authenticatedCertificate =>
          have exactAuthentication :=
            translated_immutable_deployment_success_is_exact observation
              authenticatedCertificate authenticationRun
          by_cases expectedExact :
              authenticatedCertificate.executable_sha256 =
                expectedExecutableSha256
          · have certificateExact : certificate = authenticatedCertificate := by
              simpa [authenticationRun,
                core.result.Result.Insts.CoreOpsTry.branch,
                bind_expected_executable_sha256, partial_ne_u8_array_exact,
                expectedExact] using run.symm
            subst certificate
            have observedHash :
                observation.executable_sha256 = expectedExecutableSha256 := by
              calc
                observation.executable_sha256 =
                    authenticatedCertificate.executable_sha256 :=
                  exactAuthentication.certificate_executable_sha256.symm
                _ = expectedExecutableSha256 := expectedExact
            exact ⟨exactAuthentication, observedHash⟩
          · simp [authenticationRun,
              core.result.Result.Insts.CoreOpsTry.branch,
              bind_expected_executable_sha256, partial_ne_u8_array_exact,
              expectedExact] at run

/-!
## Finite 256-bit transaction projection

The operational caller uses `u64` identities, whereas Registry V2 stores
32-byte identities.  The relation below is deliberately transaction-local:
it lists every concrete 256-bit comparison consumed by the fixed registry and
entry certificate.  It does not posit an impossible globally injective map.
-/

structure TransactionBytes32Projection where
  encode : Bytes32 → Std.U64

def TransactionBytes32Projection.ReflectsPair
    (projection : TransactionBytes32Projection)
    (left right : Bytes32) : Prop :=
  projection.encode left = projection.encode right ↔ left = right

structure RegistryTransactionIdentities where
  masterAccount : Bytes32
  registryProgram : Bytes32
  verifierProgram : Bytes32
  loaderProgram : Bytes32
  registryProgramdata : Bytes32
  verifierProgramdata : Bytes32
  profile : Bytes32
  release : Bytes32
  policyBinding : Bytes32

abbrev SourceRegistryV2 :=
  V7RegistryV2ProductionCodecsGenerated.pool_v1.verifier_registry.VerifierRegistryV2
abbrev SourceEntryV2 :=
  V7RegistryV2ProductionCodecsGenerated.pool_v1.verifier_registry.VerifierRegistryEntryV2
abbrev FixedCallerInput := V7RegistryV2OneTerminalCallerGenerated.CallerInput

def LiteralRegistryAndEntry256Fields
    (registry : SourceRegistryV2) (entry : SourceEntryV2)
    (identities : RegistryTransactionIdentities) : Prop :=
  registry.pool = identities.masterAccount ∧
  registry.authority = zero32 ∧
  registry.policy_binding = identities.policyBinding ∧
  registry.registry_program = identities.registryProgram ∧
  registry.loader_program = identities.loaderProgram ∧
  registry.programdata_address = identities.registryProgramdata ∧
  registry.executable_hash ≠ zero32 ∧
  entry.pool = identities.masterAccount ∧
  entry.verifier_program = identities.verifierProgram ∧
  entry.profile_binding = identities.profile ∧
  entry.release_binding = identities.release ∧
  entry.loader_program = identities.loaderProgram ∧
  entry.programdata_address = identities.verifierProgramdata ∧
  entry.executable_hash ≠ zero32 ∧
  entry.expected_upgrade_authority = zero32 ∧
  entry.policy_binding = identities.policyBinding

def FixedRegistryAndEntry256Fields (input : FixedCallerInput)
    (projectedEntryPolicy : Std.U64) : Prop :=
  input.registry.pool = input.master.account.key ∧
  input.registry.authority = 0#u64 ∧
  input.registry.policy_binding = input.release.policy_binding ∧
  input.registry.registry_program = input.release.registry_program ∧
  input.registry.loader_program = input.release.loader_program ∧
  input.registry.programdata_address = input.release.registry_programdata ∧
  input.registry.executable_hash ≠ 0#u64 ∧
  input.entry.pool = input.master.account.key ∧
  input.entry.verifier_program = input.release.verifier_program ∧
  input.entry.profile = input.release.profile ∧
  input.entry.release = input.release.release ∧
  input.entry.loader_program = input.release.loader_program ∧
  input.entry.programdata_address = input.release.verifier_programdata ∧
  input.entry.executable_hash ≠ 0#u64 ∧
  input.entry.expected_upgrade_authority = 0#u64 ∧
  -- Production checks this binding even though the earlier fixed caller's
  -- `ExactEntryV2Certificate` predicate did not expose it.
  projectedEntryPolicy = input.release.policy_binding

structure RegistryTransactionProjectionAgreement
    (projection : TransactionBytes32Projection)
    (registry : SourceRegistryV2) (entry : SourceEntryV2)
    (identities : RegistryTransactionIdentities)
    (input : FixedCallerInput) (projectedEntryPolicy : Std.U64) : Prop where
  zero : projection.encode zero32 = 0#u64
  registryPool : projection.encode registry.pool = input.registry.pool
  registryAuthority : projection.encode registry.authority = input.registry.authority
  registryPolicy : projection.encode registry.policy_binding = input.registry.policy_binding
  registryProgram : projection.encode registry.registry_program = input.registry.registry_program
  registryLoader : projection.encode registry.loader_program = input.registry.loader_program
  registryProgramdata :
    projection.encode registry.programdata_address = input.registry.programdata_address
  registryHash : projection.encode registry.executable_hash = input.registry.executable_hash
  entryPool : projection.encode entry.pool = input.entry.pool
  entryVerifier : projection.encode entry.verifier_program = input.entry.verifier_program
  entryProfile : projection.encode entry.profile_binding = input.entry.profile
  entryRelease : projection.encode entry.release_binding = input.entry.release
  entryLoader : projection.encode entry.loader_program = input.entry.loader_program
  entryProgramdata :
    projection.encode entry.programdata_address = input.entry.programdata_address
  entryHash : projection.encode entry.executable_hash = input.entry.executable_hash
  entryAuthority :
    projection.encode entry.expected_upgrade_authority = input.entry.expected_upgrade_authority
  entryPolicy : projection.encode entry.policy_binding = projectedEntryPolicy
  masterAccount : projection.encode identities.masterAccount = input.master.account.key
  releaseRegistryProgram :
    projection.encode identities.registryProgram = input.release.registry_program
  releaseVerifierProgram :
    projection.encode identities.verifierProgram = input.release.verifier_program
  releaseLoader : projection.encode identities.loaderProgram = input.release.loader_program
  releaseRegistryProgramdata :
    projection.encode identities.registryProgramdata = input.release.registry_programdata
  releaseVerifierProgramdata :
    projection.encode identities.verifierProgramdata = input.release.verifier_programdata
  releaseProfile : projection.encode identities.profile = input.release.profile
  releaseRelease : projection.encode identities.release = input.release.release
  releasePolicy : projection.encode identities.policyBinding = input.release.policy_binding
  registryPoolReflects : projection.ReflectsPair registry.pool identities.masterAccount
  registryAuthorityReflects : projection.ReflectsPair registry.authority zero32
  registryPolicyReflects : projection.ReflectsPair registry.policy_binding identities.policyBinding
  registryProgramReflects : projection.ReflectsPair registry.registry_program identities.registryProgram
  registryLoaderReflects : projection.ReflectsPair registry.loader_program identities.loaderProgram
  registryProgramdataReflects :
    projection.ReflectsPair registry.programdata_address identities.registryProgramdata
  registryHashReflects : projection.ReflectsPair registry.executable_hash zero32
  entryPoolReflects : projection.ReflectsPair entry.pool identities.masterAccount
  entryVerifierReflects : projection.ReflectsPair entry.verifier_program identities.verifierProgram
  entryProfileReflects : projection.ReflectsPair entry.profile_binding identities.profile
  entryReleaseReflects : projection.ReflectsPair entry.release_binding identities.release
  entryLoaderReflects : projection.ReflectsPair entry.loader_program identities.loaderProgram
  entryProgramdataReflects :
    projection.ReflectsPair entry.programdata_address identities.verifierProgramdata
  entryHashReflects : projection.ReflectsPair entry.executable_hash zero32
  entryAuthorityReflects : projection.ReflectsPair entry.expected_upgrade_authority zero32
  entryPolicyReflects : projection.ReflectsPair entry.policy_binding identities.policyBinding

theorem transaction_local_projection_iff_literal_256_fields
    (projection : TransactionBytes32Projection)
    (registry : SourceRegistryV2) (entry : SourceEntryV2)
    (identities : RegistryTransactionIdentities)
    (input : FixedCallerInput) (projectedEntryPolicy : Std.U64)
    (agreement : RegistryTransactionProjectionAgreement projection registry
      entry identities input projectedEntryPolicy) :
    FixedRegistryAndEntry256Fields input projectedEntryPolicy ↔
      LiteralRegistryAndEntry256Fields registry entry identities := by
  constructor
  · intro fixed
    rcases fixed with
      ⟨registryPool, registryAuthority, registryPolicy, registryProgram,
        registryLoader, registryProgramdata, registryHash, entryPool,
        entryVerifier, entryProfile, entryRelease, entryLoader,
        entryProgramdata, entryHash, entryAuthority, entryPolicy⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply agreement.registryPoolReflects.mp
      simpa [agreement.registryPool, agreement.masterAccount] using registryPool
    · apply agreement.registryAuthorityReflects.mp
      simpa [agreement.registryAuthority, agreement.zero] using registryAuthority
    · apply agreement.registryPolicyReflects.mp
      simpa [agreement.registryPolicy, agreement.releasePolicy] using registryPolicy
    · apply agreement.registryProgramReflects.mp
      simpa [agreement.registryProgram, agreement.releaseRegistryProgram] using registryProgram
    · apply agreement.registryLoaderReflects.mp
      simpa [agreement.registryLoader, agreement.releaseLoader] using registryLoader
    · apply agreement.registryProgramdataReflects.mp
      simpa [agreement.registryProgramdata, agreement.releaseRegistryProgramdata] using registryProgramdata
    · intro equal
      apply registryHash
      simpa [agreement.registryHash, agreement.zero] using congrArg projection.encode equal
    · apply agreement.entryPoolReflects.mp
      simpa [agreement.entryPool, agreement.masterAccount] using entryPool
    · apply agreement.entryVerifierReflects.mp
      simpa [agreement.entryVerifier, agreement.releaseVerifierProgram] using entryVerifier
    · apply agreement.entryProfileReflects.mp
      simpa [agreement.entryProfile, agreement.releaseProfile] using entryProfile
    · apply agreement.entryReleaseReflects.mp
      simpa [agreement.entryRelease, agreement.releaseRelease] using entryRelease
    · apply agreement.entryLoaderReflects.mp
      simpa [agreement.entryLoader, agreement.releaseLoader] using entryLoader
    · apply agreement.entryProgramdataReflects.mp
      simpa [agreement.entryProgramdata, agreement.releaseVerifierProgramdata] using entryProgramdata
    · intro equal
      apply entryHash
      simpa [agreement.entryHash, agreement.zero] using congrArg projection.encode equal
    · apply agreement.entryAuthorityReflects.mp
      simpa [agreement.entryAuthority, agreement.zero] using entryAuthority
    · have encodedPolicy :
          projection.encode entry.policy_binding =
            projection.encode identities.policyBinding := by
        calc
          projection.encode entry.policy_binding = input.release.policy_binding := by
            simpa [agreement.entryPolicy] using entryPolicy
          _ = projection.encode identities.policyBinding := agreement.releasePolicy.symm
      exact agreement.entryPolicyReflects.mp encodedPolicy
  · intro literal
    rcases literal with
      ⟨registryPool, registryAuthority, registryPolicy, registryProgram,
        registryLoader, registryProgramdata, registryHash, entryPool,
        entryVerifier, entryProfile, entryRelease, entryLoader,
        entryProgramdata, entryHash, entryAuthority, entryPolicy⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [← agreement.registryPool, ← agreement.masterAccount] using
        congrArg projection.encode registryPool
    · simpa [← agreement.registryAuthority, ← agreement.zero] using
        congrArg projection.encode registryAuthority
    · simpa [← agreement.registryPolicy, ← agreement.releasePolicy] using
        congrArg projection.encode registryPolicy
    · simpa [← agreement.registryProgram, ← agreement.releaseRegistryProgram] using
        congrArg projection.encode registryProgram
    · simpa [← agreement.registryLoader, ← agreement.releaseLoader] using
        congrArg projection.encode registryLoader
    · simpa [← agreement.registryProgramdata, ← agreement.releaseRegistryProgramdata] using
        congrArg projection.encode registryProgramdata
    · intro fixedZero
      apply registryHash
      apply agreement.registryHashReflects.mp
      simpa [agreement.registryHash, agreement.zero] using fixedZero
    · simpa [← agreement.entryPool, ← agreement.masterAccount] using
        congrArg projection.encode entryPool
    · simpa [← agreement.entryVerifier, ← agreement.releaseVerifierProgram] using
        congrArg projection.encode entryVerifier
    · simpa [← agreement.entryProfile, ← agreement.releaseProfile] using
        congrArg projection.encode entryProfile
    · simpa [← agreement.entryRelease, ← agreement.releaseRelease] using
        congrArg projection.encode entryRelease
    · simpa [← agreement.entryLoader, ← agreement.releaseLoader] using
        congrArg projection.encode entryLoader
    · simpa [← agreement.entryProgramdata, ← agreement.releaseVerifierProgramdata] using
        congrArg projection.encode entryProgramdata
    · intro fixedZero
      apply entryHash
      apply agreement.entryHashReflects.mp
      simpa [agreement.entryHash, agreement.zero] using fixedZero
    · simpa [← agreement.entryAuthority, ← agreement.zero] using
        congrArg projection.encode entryAuthority
    · have encoded :
          projection.encode entry.policy_binding =
            projection.encode identities.policyBinding := congrArg projection.encode entryPolicy
      calc
        projectedEntryPolicy = projection.encode entry.policy_binding := agreement.entryPolicy.symm
        _ = projection.encode identities.policyBinding := encoded
        _ = input.release.policy_binding := agreement.releasePolicy

theorem literal_256_fields_supply_fixed_caller_certificate_fields
    (projection : TransactionBytes32Projection)
    (registry : SourceRegistryV2) (entry : SourceEntryV2)
    (identities : RegistryTransactionIdentities)
    (input : FixedCallerInput) (projectedEntryPolicy : Std.U64)
    (agreement : RegistryTransactionProjectionAgreement projection registry
      entry identities input projectedEntryPolicy)
    (literal : LiteralRegistryAndEntry256Fields registry entry identities) :
    FixedRegistryAndEntry256Fields input projectedEntryPolicy :=
  (transaction_local_projection_iff_literal_256_fields projection registry
    entry identities input projectedEntryPolicy agreement).2 literal

#print axioms partial_ne_u8_array_exact
#print axioms translated_immutable_deployment_success_is_exact
#print axioms translated_deployment_source_root_success_is_exact
#print axioms transaction_local_projection_iff_literal_256_fields
#print axioms literal_256_fields_supply_fixed_caller_certificate_fields

end

end V7RegistryV2DeploymentCertificateGenerated
