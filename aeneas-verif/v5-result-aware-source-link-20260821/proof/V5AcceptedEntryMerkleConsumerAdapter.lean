import V5AcceptedEntryMerkleEndToEnd
import V5MerkleFriReturnedOutputBridge

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5AcceptedEntryMerkleConsumerAdapter

open AspisV5AcceptedEntryMerkleEndToEnd
open AspisV5FriConsumerObservationBridge
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleConsumedValueBridge
open AspisV5MerkleRustBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

/-- The two generated namespace adapters for the same returned Rust value
compose to the direct structural conversion used by the FRI proof. -/
theorem entry_openings_to_consumer_verified_from_exact
    (exactOpening : ExactOpenings) :
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.openingsToConsumer
        (V5AcceptedEntryGenerated.v5_cu_probe.private_openings.verifiedFromExact
          exactOpening) =
      AspisV5MerkleFriReturnedOutputBridge.toFriVerified exactOpening := by
  rcases exactOpening with ⟨c1, c2, later, indices, bytesConsumed⟩
  have openingConversion
      (opening :
        V5MerkleUnchangedFull.aspis_core.state_only_private_openings.StateOnlyPrivateOpening) :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.openingToConsumer
          (V5AcceptedEntryGenerated.v5_cu_probe.private_openings.openingFromExact
            opening) =
        AspisV5MerkleFriReturnedOutputBridge.toFriOpening opening := by
    rcases opening with ⟨count, valueWidth, records, frontier, offsets⟩
    rfl
  simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.openingsToConsumer,
    V5AcceptedEntryGenerated.v5_cu_probe.private_openings.verifiedFromExact,
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.consumerMapArray,
    V5AcceptedEntryGenerated.v5_cu_probe.private_openings.mapExactArray,
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.openingToConsumer,
    V5AcceptedEntryGenerated.v5_cu_probe.private_openings.openingFromExact,
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.offsetsToConsumer,
    V5AcceptedEntryGenerated.v5_cu_probe.private_openings.offsetsFromExact,
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.indicesToConsumer,
    V5AcceptedEntryGenerated.v5_cu_probe.private_openings.indicesFromExact,
    AspisV5MerkleFriReturnedOutputBridge.toFriVerified,
    AspisV5MerkleFriReturnedOutputBridge.toFriOpening,
    AspisV5MerkleFriReturnedOutputBridge.toFriOffsets,
    AspisV5MerkleFriReturnedOutputBridge.toFriQueryIndices,
    AspisV5MerkleFriReturnedOutputBridge.mapArray, List.map_map]
  apply Subtype.ext
  apply List.map_congr_left
  intro opening _
  exact openingConversion opening

/-- Resolver containing exactly the accepted FRI call belonging to one
accepted production execution. -/
noncomputable def singleAcceptedEntryResolver
    (target : V5ProductionCall) (acceptedCall : AcceptedFriCall) :
    V5ProductionCall → Option AcceptedFriCall :=
  fun call => by
    classical
    exact if call = target then some acceptedCall else none

@[simp] theorem singleAcceptedEntryResolver_target
    (target : V5ProductionCall) (acceptedCall : AcceptedFriCall) :
    singleAcceptedEntryResolver target acceptedCall target =
      some acceptedCall := by
  simp [singleAcceptedEntryResolver]

/-- One exact Merkle run and one successful FRI call are enough to prove the
parser/output half for the corresponding one-call observation. -/
theorem singleAcceptedEntryResolver_parser_equality
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (target : V5ProductionCall)
    (acceptedCall : AcceptedFriCall)
    (run : ExactV5Run sha256 target.roots target.queries)
    (proofBytes : run.proofBytes = target.proofBytes)
    (driver :
      AspisV5FriConsumerObservationBridge.generatedDriverOutput
          acceptedCall.openings =
        AspisV5MerkleConsumedValueBridge.driverOutputOfRun run []) :
    ExactRustV5OpeningParserOutputEquality sha256
      (observationFromAcceptedResolver
        (singleAcceptedEntryResolver target acceptedCall)) := by
  intro call observation observed
  unfold observationFromAcceptedResolver singleAcceptedEntryResolver at observed
  split at observed
  · next equal =>
      subst call
      simp only [Option.map_some, Option.some.injEq] at observed
      subst observation
      exact ⟨run, proofBytes, driver⟩
  · simp at observed

/-- The concrete source-shaped four-loop schedule then closes the combined
opening-parser and FRI-consumer equality for this same accepted call. -/
theorem singleAcceptedEntryResolver_consumer_equality
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (target : V5ProductionCall)
    (acceptedCall : AcceptedFriCall)
    (run : ExactV5Run sha256 target.roots target.queries)
    (proofBytes : run.proofBytes = target.proofBytes)
    (driver :
      AspisV5FriConsumerObservationBridge.generatedDriverOutput
          acceptedCall.openings =
        AspisV5MerkleConsumedValueBridge.driverOutputOfRun run []) :
    ExactRustV5OpeningAndFriConsumerEquality sha256
      (observationFromAcceptedResolver
        (singleAcceptedEntryResolver target acceptedCall)) :=
  opening_parser_and_accepted_resolver_imply_consumer_equality sha256
    (singleAcceptedEntryResolver target acceptedCall)
    (singleAcceptedEntryResolver_parser_equality sha256 target acceptedCall
      run proofBytes driver)

/-- A source-independent one-call observation.  It carries only the returned
driver value and the literal four-loop read schedule, so its reusable theorem
does not mention any generated FRI helper. -/
noncomputable def singleDriverObservation
    (target : V5ProductionCall) (driver : V5DriverOutput) :
    V5ProductionCall → Option OpeningAndFriObservation :=
  fun call => by
    classical
    exact if call = target then
      some ⟨driver,
        AspisV5FriSourceLoopOrder.sourceShapedFriReadSchedule driver⟩
    else none

@[simp] theorem singleDriverObservation_target
    (target : V5ProductionCall) (driver : V5DriverOutput) :
    singleDriverObservation target driver target =
      some ⟨driver,
        AspisV5FriSourceLoopOrder.sourceShapedFriReadSchedule driver⟩ := by
  simp [singleDriverObservation]

theorem singleDriverObservation_parser_equality
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (target : V5ProductionCall)
    (run : ExactV5Run sha256 target.roots target.queries)
    (proofBytes : run.proofBytes = target.proofBytes) :
    ExactRustV5OpeningParserOutputEquality sha256
      (singleDriverObservation target
        (AspisV5MerkleConsumedValueBridge.driverOutputOfRun run [])) := by
  intro call observation observed
  unfold singleDriverObservation at observed
  split at observed
  · next equal =>
      subst call
      simp only [Option.some.injEq] at observed
      subst observation
      exact ⟨run, proofBytes, rfl⟩
  · simp at observed

theorem singleDriverObservation_read_trace
    (target : V5ProductionCall) (driver : V5DriverOutput) :
    AspisV5FriSourceLoopOrder.CheckV5FriQueriesSuccessfulReadTraceEquality
      (singleDriverObservation target driver) := by
  intro call observation observed
  unfold singleDriverObservation at observed
  split at observed
  · simp only [Option.some.injEq] at observed
    subst observation
    rfl
  · simp at observed

/-- Reusable standard-foundation closure: once a run and its exact parser
output are fixed, the deterministic source-shaped read schedule is the exact
maintained FRI schedule.  No generated Rust helper occurs in this statement. -/
theorem singleDriverObservation_consumer_equality
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (target : V5ProductionCall)
    (run : ExactV5Run sha256 target.roots target.queries)
    (proofBytes : run.proofBytes = target.proofBytes) :
    ExactRustV5OpeningAndFriConsumerEquality sha256
      (singleDriverObservation target
        (AspisV5MerkleConsumedValueBridge.driverOutputOfRun run [])) :=
  AspisV5FriSourceLoopOrder.openingParser_and_checkV5FriQueriesReadTrace_imply_consumerEquality
    sha256
    (singleDriverObservation target
      (AspisV5MerkleConsumedValueBridge.driverOutputOfRun run []))
    (singleDriverObservation_parser_equality sha256 target run proofBytes)
    (singleDriverObservation_read_trace target
      (AspisV5MerkleConsumedValueBridge.driverOutputOfRun run []))

end AspisV5AcceptedEntryMerkleConsumerAdapter
