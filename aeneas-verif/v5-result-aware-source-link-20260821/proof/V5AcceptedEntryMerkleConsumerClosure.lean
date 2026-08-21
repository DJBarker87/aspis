import V5AcceptedEntryMerkleConsumerAdapter
import V5AcceptedEntryMerkleQueryAlignment
import V5AcceptedTranscriptQueryBridge
import V5MerkleUnchangedPublicAcceptanceBridge

/-!
# Accepted entry Merkle/FRI consumer closure

This final production corollary is kept separate from the reusable,
axiom-free resolver theorem so the source-specific trust boundary remains
easy to audit.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5AcceptedEntryMerkleConsumerClosure

open AspisV5AcceptedEntryFriPhaseBridge
open AspisV5AcceptedEntryMerkleConsumerAdapter
open AspisV5AcceptedEntryMerkleEndToEnd
open AspisV5AcceptedEntryMerkleQueryAlignment
open AspisV5AcceptedEntrySourceBridge
open AspisV5AcceptedSameRunRelationFriSnapshot
open AspisV5AcceptedTranscriptQueryBridge
open AspisV5AcceptedExecutionDerivedQueries
open AspisV5FriConsumerObservationBridge
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleConsumedValueBridge
open AspisV5MerkleRustBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

/-- One accepted composite execution supplies, without a caller-environment
premise, the exact 18-query Merkle run and the exact FRI consumer observation.
The only executable semantic premise introduced here is the named equality
between the Solana hash callback and the mathematical SHA-256 function. -/
theorem accepted_snapshot_builds_exact_merkle_consumer
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hhash :
      AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
        sha256 V5AcceptedEntryGenerated.verify.sbf_hashv_totalized) :
    ∃ (blocks : List (AspisV5TranscriptConnection.FixedBytes 32))
        (hdecode : AspisV5TranscriptConnection.derive18Queries blocks =
          some (snapshot.queries.val.map UScalar.val))
        (rootsArray : Array
          AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedDigest 5#usize)
        (modelRoots : V5PrivateRoots Digest32)
        (run : ExactV5Run sha256 modelRoots
          (decodedQuerySet blocks
            (snapshot.queries.val.map UScalar.val) hdecode)),
      (V5AcceptedEntryGenerated.v5_cu_probe.private_openings.rootsToExact
          parsed.v5_private_roots).as_array = .ok rootsArray ∧
      AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedRootsMatch
        rootsArray modelRoots ∧
      run.proofBytes = parsed.v5_private_proof.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte ∧
      let target : V5ProductionCall :=
        { roots := modelRoots
          queries := decodedQuerySet blocks
            (snapshot.queries.val.map UScalar.val) hdecode
          proofBytes := parsed.v5_private_proof.val.map
            AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte }
      singleAcceptedEntryResolver target snapshot.acceptedFriCall target =
          some snapshot.acceptedFriCall ∧
        ExactRustV5OpeningAndFriConsumerEquality sha256
          (observationFromAcceptedResolver
            (singleAcceptedEntryResolver target snapshot.acceptedFriCall)) := by
  have successor := selected_query_success_has_final_successor
    snapshot.relationTranscript parsed snapshot.verifiedPrefix.round_challenges
    snapshot.finalPolynomial snapshot.queries
    snapshot.evidence.compositeCalls.querySuccess
  have sampler := accepted_final_query_successor_is_exact_sampler parsed
    snapshot.queries successor
  obtain ⟨blocks, hdecode, _scheduleValues, _querySetImage, queryCount,
      _queryNodup, _queryRange⟩ :=
    accepted_query_sampler_builds_decoded_schedule parsed snapshot.queries
      sampler
  obtain ⟨exactOpening, merkleSuccess, returnedOpening,
      _c1Records, _c2Records⟩ :=
    private_suffix_success_yields_exact_merkle parsed snapshot.queries
      snapshot.openings snapshot.evidence.exactFriCalls.privateSuffixSuccess
  have queryModel := accepted_queries_model_exact_merkle_layer_zero
    blocks snapshot.queries hdecode
  obtain ⟨rootsArray, modelRoots, run, rootsEq, rootsMatch, proofBytes,
      merkleDriver⟩ :=
    AspisV5MerkleUnchangedPublicAcceptanceBridge.generated_public_acceptance_yields_exact_v5_with_output
      sha256
      (decodedQuerySet blocks (snapshot.queries.val.map UScalar.val) hdecode)
      queryCount V5AcceptedEntryGenerated.verify.sbf_hashv_totalized
      (V5AcceptedEntryGenerated.v5_cu_probe.private_openings.rootsToExact
        parsed.v5_private_roots)
      (Array.to_slice snapshot.queries) parsed.v5_private_proof exactOpening
      hhash queryModel merkleSuccess
  have acceptedOpening : snapshot.acceptedFriCall.openings =
      AspisV5MerkleFriReturnedOutputBridge.toFriVerified exactOpening := by
    calc
      snapshot.acceptedFriCall.openings =
          V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.openingsToConsumer
            snapshot.openings := snapshot.acceptedFriOpenings
      _ = V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.openingsToConsumer
            (V5AcceptedEntryGenerated.v5_cu_probe.private_openings.verifiedFromExact
              exactOpening) := by rw [returnedOpening]
      _ = AspisV5MerkleFriReturnedOutputBridge.toFriVerified exactOpening :=
        entry_openings_to_consumer_verified_from_exact exactOpening
  have consumerDriver :
      AspisV5FriConsumerObservationBridge.generatedDriverOutput
          snapshot.acceptedFriCall.openings =
        AspisV5MerkleConsumedValueBridge.driverOutputOfRun run [] := by
    rw [acceptedOpening]
    exact AspisV5MerkleFriReturnedOutputBridge.converted_driver_output_eq_run
      run exactOpening merkleDriver
  let target : V5ProductionCall :=
    { roots := modelRoots
      queries := decodedQuerySet blocks
        (snapshot.queries.val.map UScalar.val) hdecode
      proofBytes := parsed.v5_private_proof.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte }
  refine ⟨blocks, hdecode, rootsArray, modelRoots, run, rootsEq, rootsMatch,
    proofBytes, ?_⟩
  exact ⟨singleAcceptedEntryResolver_target target snapshot.acceptedFriCall,
    singleAcceptedEntryResolver_consumer_equality sha256 target
      snapshot.acceptedFriCall run proofBytes consumerDriver⟩

end AspisV5AcceptedEntryMerkleConsumerClosure
