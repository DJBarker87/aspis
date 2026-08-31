import V7PairForestProductionCodecSourceBridge
import V7RegistryV2DeploymentCertificateSourceBridge

/-!
# Registry V2 / ASQ8 / ASR8 accepted-path composition

This file composes the literal translated ASQ8 reconstruction and ASR8
emission functions with the translated Registry V2 atomic caller and the
literal loader-v3 deployment-certificate roots.

The fixed-width caller is an operational projection, so the two structures
named `...ProjectionAgreement` below state only finite representation
equalities for this transaction.  They do not assert verifier acceptance,
writeback, cryptographic soundness, or rollback.  Those conclusions still
come from successful translated executions.

The current literal `process_with_clear_return_data` / `verify_statement_v1`
join is intentionally not represented as a theorem premise pretending to be
source translation.  Aeneas cannot yet translate that `AccountInfo` borrow
join.  Consequently this theorem closes every independently translated source
piece around that join and leaves the join itself as the single explicit
production-call boundary.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16000

namespace V7RegistryV2ProductionCallComposition

open Aeneas Aeneas.Std Result ControlFlow Error

abbrev CodecRequest :=
  V7PairForestProductionCodecsGenerated.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev CodecStatement :=
  V7PairForestProductionCodecsGenerated.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev CodecResult :=
  V7PairForestProductionCodecsGenerated.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
abbrev CodecAuthenticated :=
  V7PairForestProductionCodecsGenerated.v7_pair_forest_dispatch.AuthenticatedV7PairForestAsq8AccountsV1
abbrev CodecAfterstate :=
  V7PairForestProductionCodecsGenerated.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev CodecDigest :=
  Array V7PairForestProductionCodecsGenerated.aspis_core.field.M31 8#usize
abbrev CodecFrontier := Array CodecDigest 20#usize
abbrev EncodedASR8 := Array Std.U8 792#usize

abbrev CallerInput := V7RegistryV2OneTerminalCallerGenerated.CallerInput
abbrev CallerResult := V7RegistryV2OneTerminalCallerGenerated.ReturnedResult
abbrev CallerImages := V7RegistryV2OneTerminalCallerGenerated.PoolImages
abbrev CallerOutcome := V7RegistryV2OneTerminalCallerGenerated.TransactionOutcome
abbrev CallerAccepted := V7RegistryV2OneTerminalCallerGenerated.AcceptedExecution
abbrev CallerPaymentKind := V7RegistryV2OneTerminalCallerGenerated.PaymentKind

abbrev Bytes32Projection :=
  V7RegistryV2DeploymentCertificateGenerated.TransactionBytes32Projection
abbrev SourceRegistryV2 :=
  V7RegistryV2DeploymentCertificateGenerated.SourceRegistryV2
abbrev SourceEntryV2 :=
  V7RegistryV2DeploymentCertificateGenerated.SourceEntryV2
abbrev RegistryIdentities :=
  V7RegistryV2DeploymentCertificateGenerated.RegistryTransactionIdentities
abbrev RegistryProjectionAgreement :=
  V7RegistryV2DeploymentCertificateGenerated.RegistryTransactionProjectionAgreement
abbrev DeploymentObservation :=
  V7RegistryV2DeploymentCertificateGenerated.DeploymentObservation
abbrev DeploymentCertificate :=
  V7RegistryV2DeploymentCertificateGenerated.ImmutableDeploymentCertificate

/-- The only non-byte fixed-width values used by the operational caller. -/
structure TerminalProjection where
  digest : CodecDigest → Std.U64
  frontier : CodecFrontier → Std.U64
  encodedId : EncodedASR8 → Std.U64

def projectKind :
    V7PairForestProductionCodecsGenerated.aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind →
      CallerPaymentKind
  | .PrivateTransfer => .PrivateTransfer
  | .Withdrawal => .Withdrawal

def projectCodecResult (bytes : Bytes32Projection)
    (terminal : TerminalProjection) (result : CodecResult) : CallerResult := {
  transition_kind := projectKind result.transition_kind
  master_account := bytes.encode result.master_account
  selected_lane_account := bytes.encode result.selected_lane_account
  output_lane := result.output_lane
  nullifier := terminal.digest result.nullifier
  next_pair_index := result.verified_afterstate.next_pair_index
  next_root := terminal.digest result.verified_afterstate.next_root
  next_frontier := terminal.frontier result.verified_afterstate.next_frontier
  next_frontier_canonical := true
}

def requestKind (request : CodecRequest) : CallerPaymentKind :=
  match request.«public» with
  | .PrivateTransfer _ => .PrivateTransfer
  | .Withdrawal _ => .Withdrawal

def requestPool (request : CodecRequest) : Array Std.U8 32#usize :=
  match request.«public» with
  | .PrivateTransfer payment => payment.pool
  | .Withdrawal payment => payment.pool

def requestDeploymentDomain (request : CodecRequest) : Array Std.U8 32#usize :=
  match request.«public» with
  | .PrivateTransfer payment => payment.deployment_domain
  | .Withdrawal payment => payment.deployment_domain

def requestAnchorSequence (request : CodecRequest) : Std.U64 :=
  match request.«public» with
  | .PrivateTransfer payment => payment.anchor_sequence
  | .Withdrawal payment => payment.anchor_sequence

def requestAnchorRoot (request : CodecRequest) : CodecDigest :=
  match request.«public» with
  | .PrivateTransfer payment => payment.anchor_root
  | .Withdrawal payment => payment.anchor_root

def requestNullifier (request : CodecRequest) : CodecDigest :=
  match request.«public» with
  | .PrivateTransfer payment => payment.nullifier
  | .Withdrawal payment => payment.nullifier

/-!
These are transaction-local representation equalities.  In particular, no
globally injective `bytes32 → u64` or digest compression is asserted.
-/
structure VerifierCallerStatementProjectionAgreement
    (bytes : Bytes32Projection) (terminal : TerminalProjection)
    (request : CodecRequest) (authenticated : CodecAuthenticated)
    (candidate : CodecAfterstate) (input : CallerInput) : Prop where
  profile : bytes.encode request.verifier_profile = input.request.profile
  release : bytes.encode request.verifier_release = input.request.release
  poolProgram : bytes.encode request.pool_program = input.request.pool_program
  masterAccount :
    bytes.encode authenticated.master_account = input.master.account.key
  checkpointAccount :
    bytes.encode authenticated.checkpoint_account = input.checkpoint.account.key
  selectedLaneAccount :
    bytes.encode authenticated.selected_lane_account = input.lane.account.key
  outputLane : authenticated.selected_lane.lane_id = input.request.output_lane
  paymentKind : requestKind request = input.request.payment_kind
  paymentPool : bytes.encode (requestPool request) = input.master.account.key
  deploymentDomain :
    bytes.encode (requestDeploymentDomain request) =
      input.master.deployment_domain
  anchorSequence : requestAnchorSequence request = input.checkpoint.sequence
  anchorRoot :
    terminal.digest (requestAnchorRoot request) = input.checkpoint.global_root
  nullifier :
    terminal.digest (requestNullifier request) = input.request.nullifier
  checkpointSequence :
    authenticated.checkpoint.checkpoint_sequence = input.checkpoint.sequence
  historicalAnchor :
    terminal.digest authenticated.checkpoint.global_root =
      input.checkpoint.global_root
  liveNextPairIndex :
    authenticated.live_snapshot.next_pair_index = input.lane.next_pair_index
  liveRoot :
    terminal.digest authenticated.live_snapshot.current_root = input.lane.root
  liveFrontier :
    terminal.frontier authenticated.live_snapshot.frontier = input.lane.frontier
  candidateNextPairIndex :
    U64.checked_add input.lane.next_pair_index 1#u64 =
      some candidate.next_pair_index

/-- Correspondence between literal canonical ASR8 bytes and the operational
caller's finite return-data projection.  This contains representation
equalities only; it does not state that either verifier or caller accepts. -/
structure ImmediateResultProjectionAgreement
    (bytes : Bytes32Projection) (terminal : TerminalProjection)
    (statement : CodecStatement) (input : CallerInput) : Prop where
  decoded :
    input.verifier_return.decoded =
      some (projectCodecResult bytes terminal
        (V7PairForestProductionCodecsGenerated.ProductionCodecSourceBridge.exactResult
          statement))
  encodedIdentity : ∀ encoded : EncodedASR8,
    V7PairForestProductionCodecsGenerated.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1
        (V7PairForestProductionCodecsGenerated.ProductionCodecSourceBridge.exactResult
          statement) = .ok (.Ok encoded) →
      input.verifier_return.exact_bytes_id = terminal.encodedId encoded

/-- Literal loader-v3 observations refer to the same Registry V2 records used
by the transaction-local projection. -/
structure DeploymentPairAgreement
    (registry : SourceRegistryV2) (entry : SourceEntryV2)
    (registryObservation verifierObservation : DeploymentObservation) : Prop where
  registryProgram :
    registryObservation.expected_program = registry.registry_program
  registryLoader : registryObservation.loader_v3 = registry.loader_program
  registryProgramdata :
    registryObservation.programdata_account.key = registry.programdata_address
  verifierProgram :
    verifierObservation.expected_program = entry.verifier_program
  verifierLoader : verifierObservation.loader_v3 = entry.loader_program
  verifierProgramdata :
    verifierObservation.programdata_account.key = entry.programdata_address

def ExactComposedAcceptedPath
    (bytes : Bytes32Projection) (terminal : TerminalProjection)
    (request : CodecRequest) (authenticated : CodecAuthenticated)
    (candidate : CodecAfterstate) (statement : CodecStatement)
    (input : CallerInput) (before : CallerImages) (out : CallerOutcome)
    (registry : SourceRegistryV2) (entry : SourceEntryV2)
    (identities : RegistryIdentities)
    (registryObservation verifierObservation : DeploymentObservation)
    (registryCertificate verifierCertificate : DeploymentCertificate) : Prop :=
  ∃ caller : CallerAccepted, ∃ encoded : EncodedASR8,
    V7RegistryV2OneTerminalCallerGenerated.execute_terminal_caller input before =
        .ok (.Ok caller) ∧
    out.state = caller.state ∧
    out.certificate = some caller.certificate ∧
    out.error = none ∧
    V7RegistryV2OneTerminalCallerGenerated.ExactAcceptedWriteback
        input before caller ∧
    statement =
      V7PairForestProductionCodecsGenerated.ProductionCodecSourceBridge.exactStatement
        request authenticated candidate ∧
    V7PairForestProductionCodecsGenerated.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_result_against_statement_v1
        statement
        (V7PairForestProductionCodecsGenerated.ProductionCodecSourceBridge.exactResult
          statement) = .ok (.Ok ()) ∧
    V7PairForestProductionCodecsGenerated.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1
        (V7PairForestProductionCodecsGenerated.ProductionCodecSourceBridge.exactResult
          statement) = .ok (.Ok encoded) ∧
    caller.certificate.result =
      projectCodecResult bytes terminal
        (V7PairForestProductionCodecsGenerated.ProductionCodecSourceBridge.exactResult
          statement) ∧
    caller.certificate.result_bytes_id = terminal.encodedId encoded ∧
    out.state.returned_result = some
      (projectCodecResult bytes terminal
        (V7PairForestProductionCodecsGenerated.ProductionCodecSourceBridge.exactResult
          statement)) ∧
    out.state.returned_result_bytes_id = some (terminal.encodedId encoded) ∧
    VerifierCallerStatementProjectionAgreement bytes terminal request
      authenticated candidate input ∧
    V7RegistryV2DeploymentCertificateGenerated.LiteralRegistryAndEntry256Fields
      registry entry identities ∧
    V7RegistryV2DeploymentCertificateGenerated.FixedRegistryAndEntry256Fields
      input (bytes.encode entry.policy_binding) ∧
    DeploymentPairAgreement registry entry registryObservation
      verifierObservation ∧
    V7RegistryV2DeploymentCertificateGenerated.ExactDeploymentSourceRootSuccess
      registryObservation registry.executable_hash registryCertificate ∧
    V7RegistryV2DeploymentCertificateGenerated.ExactDeploymentSourceRootSuccess
      verifierObservation entry.executable_hash verifierCertificate

theorem translated_components_compose_exact_accepted_path
    (bytes : Bytes32Projection) (terminal : TerminalProjection)
    (request : CodecRequest) (authenticated : CodecAuthenticated)
    (candidate : CodecAfterstate) (statement : CodecStatement)
    (input : CallerInput) (before : CallerImages) (out : CallerOutcome)
    (registry : SourceRegistryV2) (entry : SourceEntryV2)
    (identities : RegistryIdentities)
    (registryProjection : RegistryProjectionAgreement bytes registry entry
      identities input (bytes.encode entry.policy_binding))
    (literalRegistry :
      V7RegistryV2DeploymentCertificateGenerated.LiteralRegistryAndEntry256Fields
        registry entry identities)
    (registryObservation verifierObservation : DeploymentObservation)
    (registryCertificate verifierCertificate : DeploymentCertificate)
    (deploymentProjection :
      DeploymentPairAgreement registry entry registryObservation
        verifierObservation)
    (registryDeploymentRun :
      V7RegistryV2DeploymentCertificateGenerated.deployment_certificate_source_roots
        registryObservation registry.executable_hash =
          .ok (.Ok registryCertificate))
    (verifierDeploymentRun :
      V7RegistryV2DeploymentCertificateGenerated.deployment_certificate_source_roots
        verifierObservation entry.executable_hash =
          .ok (.Ok verifierCertificate))
    (statementProjection :
      VerifierCallerStatementProjectionAgreement bytes terminal request
        authenticated candidate input)
    (reconstructionRun :
      V7PairForestProductionCodecsGenerated.v7_pair_forest_dispatch.reconstruct_asq8_statement_box_v1
          request authenticated candidate = .ok (.Ok statement))
    (emissionRun :
      V7PairForestProductionCodecsGenerated.v7_pair_forest_dispatch.emit_result_v1
          statement = .ok (.Ok ()))
    (returnProjection :
      ImmediateResultProjectionAgreement bytes terminal statement input)
    (callerRun :
      V7RegistryV2OneTerminalCallerGenerated.execute_atomic_transaction
          input before = .ok out)
    (accepted : out.committed = true) :
    ExactComposedAcceptedPath bytes terminal request authenticated candidate
      statement input before out registry entry identities registryObservation
      verifierObservation registryCertificate verifierCertificate := by
  have statementExact :=
    V7PairForestProductionCodecsGenerated.ProductionCodecSourceBridge.translated_reconstruction_success_is_exact
      request authenticated candidate statement reconstructionRun
  obtain ⟨encoded, resultValidation, resultEncoding⟩ :=
    V7PairForestProductionCodecsGenerated.ProductionCodecSourceBridge.translated_emit_success_has_exact_canonical_result
      statement emissionRun
  obtain ⟨caller, exactCallerRun, stateExact, certificateExact, errorExact,
      writeback⟩ :=
    V7RegistryV2OneTerminalCallerGenerated.translated_accepted_atomic_transaction_has_exact_writeback
      input before out callerRun accepted
  have registryDeployment :=
    V7RegistryV2DeploymentCertificateGenerated.translated_deployment_source_root_success_is_exact
      registryObservation registry.executable_hash registryCertificate
        registryDeploymentRun
  have verifierDeployment :=
    V7RegistryV2DeploymentCertificateGenerated.translated_deployment_source_root_success_is_exact
      verifierObservation entry.executable_hash verifierCertificate
        verifierDeploymentRun
  have fixedRegistry :=
    V7RegistryV2DeploymentCertificateGenerated.literal_256_fields_supply_fixed_caller_certificate_fields
      bytes registry entry identities input (bytes.encode entry.policy_binding)
        registryProjection literalRegistry
  have writebackParts := writeback
  rcases writebackParts with
    ⟨_, resultBinding, _, finalized, _, _, _, _⟩
  rcases resultBinding with
    ⟨_, _, _, _, decodedCaller, _, _, _, _, _, _, _⟩
  rcases finalized with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, returnedResult,
      resultBytes, returnedBytes, _⟩
  have projectedResultExact :
      caller.certificate.result =
        projectCodecResult bytes terminal
          (V7PairForestProductionCodecsGenerated.ProductionCodecSourceBridge.exactResult
            statement) := by
    exact Option.some.inj (decodedCaller.symm.trans returnProjection.decoded)
  have projectedResultBytesExact :
      caller.certificate.result_bytes_id = terminal.encodedId encoded :=
    resultBytes.trans (returnProjection.encodedIdentity encoded resultEncoding)
  have returnedStateResultExact :
      out.state.returned_result = some
        (projectCodecResult bytes terminal
          (V7PairForestProductionCodecsGenerated.ProductionCodecSourceBridge.exactResult
            statement)) := by
    calc
      out.state.returned_result = caller.state.returned_result :=
        congrArg (fun state => state.returned_result) stateExact
      _ = some caller.certificate.result := returnedResult
      _ = some (projectCodecResult bytes terminal
          (V7PairForestProductionCodecsGenerated.ProductionCodecSourceBridge.exactResult
            statement)) := congrArg some projectedResultExact
  have returnedStateBytesExact :
      out.state.returned_result_bytes_id = some (terminal.encodedId encoded) := by
    calc
      out.state.returned_result_bytes_id =
          caller.state.returned_result_bytes_id :=
        congrArg (fun state => state.returned_result_bytes_id) stateExact
      _ = some input.verifier_return.exact_bytes_id := returnedBytes
      _ = some (terminal.encodedId encoded) :=
        congrArg some (returnProjection.encodedIdentity encoded resultEncoding)
  exact ⟨caller, encoded, exactCallerRun, stateExact, certificateExact,
    errorExact, writeback, statementExact, resultValidation, resultEncoding,
    projectedResultExact, projectedResultBytesExact, returnedStateResultExact,
    returnedStateBytesExact, statementProjection, literalRegistry,
    fixedRegistry, deploymentProjection, registryDeployment,
    verifierDeployment⟩

#print axioms translated_components_compose_exact_accepted_path

end V7RegistryV2ProductionCallComposition
