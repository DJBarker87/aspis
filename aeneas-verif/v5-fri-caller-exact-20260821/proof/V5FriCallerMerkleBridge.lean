import V5FriCallerParametric
import V5MerkleFriReturnedOutputBridge

/-!
# Exact Merkle result used by the production FRI caller

The caller and the Merkle verifier were translated in separate Aeneas runs,
so their copies of the Rust opening structs have different Lean names. This
file gives the field-for-field conversion and combines the caller's accepted
call trace with the exact Merkle public-acceptance theorem.

The remaining tool edge is deliberately narrow.  The hash-pinned replay patch
adds a first-order wrapper containing one call to the unchanged Merkle helper
with the production hash callback.  Charon records the caller's call to that
wrapper, while Aeneas leaves the wrapper itself opaque.  The explicit model
below connects that checked source edge to the independent unchanged-helper
translation; it is not a claim that Aeneas translated the wrapper body.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriCallerMerkleBridge

namespace Caller
open V5FriCaller

abbrev Roots := v5_cu_probe.private_openings.V5PrivateOpeningRoots
abbrev Opening :=
  aspis_core.state_only_private_openings.StateOnlyPrivateOpening
abbrev Offsets :=
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningOffsets
abbrev Indices := aspis_core.circle_line_merkle.CircleLineQueryIndices
abbrev Verified := v5_cu_probe.private_openings.VerifiedV5PrivateOpenings
abbrev Error := v5_cu_probe.private_openings.V5PrivateOpeningError

end Caller

namespace Merkle
open V5MerkleUnchangedFull

abbrev Roots := private_openings.V5PrivateOpeningRoots
abbrev Opening :=
  aspis_core.state_only_private_openings.StateOnlyPrivateOpening
abbrev Offsets :=
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningOffsets
abbrev Indices := aspis_core.circle_line_merkle.CircleLineQueryIndices
abbrev Verified := private_openings.VerifiedV5PrivateOpenings

end Merkle

def mapArray {A B : Type*} {n : Std.Usize} (f : A → B)
    (values : Array A n) : Array B n :=
  ⟨values.val.map f, by simpa using values.property⟩

def toMerkleRoots (roots : Caller.Roots) : Merkle.Roots where
  c1 := roots.c1
  c2 := roots.c2
  later := roots.later

def toMerkleOffsets (offsets : Caller.Offsets) : Merkle.Offsets where
  count := offsets.count
  records := offsets.records
  frontier_count := offsets.frontier_count
  frontier := offsets.frontier
  «end» := offsets.end

def toMerkleOpening (opening : Caller.Opening) : Merkle.Opening where
  count := opening.count
  value_width := opening.value_width
  records := opening.records
  frontier := opening.frontier
  offsets := toMerkleOffsets opening.offsets

def toMerkleIndices (indices : Caller.Indices) : Merkle.Indices where
  layer0 := indices.layer0
  later := indices.later

def toMerkleVerified (verified : Caller.Verified) : Merkle.Verified where
  c1 := toMerkleOpening verified.c1
  c2 := toMerkleOpening verified.c2
  later := mapArray toMerkleOpening verified.later
  indices := toMerkleIndices verified.indices
  bytes_consumed := verified.bytes_consumed

def fromMerkleOffsets (offsets : Merkle.Offsets) : Caller.Offsets where
  count := offsets.count
  records := offsets.records
  frontier_count := offsets.frontier_count
  frontier := offsets.frontier
  «end» := offsets.end

def fromMerkleOpening (opening : Merkle.Opening) : Caller.Opening where
  count := opening.count
  value_width := opening.value_width
  records := opening.records
  frontier := opening.frontier
  offsets := fromMerkleOffsets opening.offsets

def fromMerkleIndices (indices : Merkle.Indices) : Caller.Indices where
  layer0 := indices.layer0
  later := indices.later

def fromMerkleVerified (verified : Merkle.Verified) : Caller.Verified where
  c1 := fromMerkleOpening verified.c1
  c2 := fromMerkleOpening verified.c2
  later := mapArray fromMerkleOpening verified.later
  indices := fromMerkleIndices verified.indices
  bytes_consumed := verified.bytes_consumed

@[simp] theorem toMerkleOffsets_fromMerkleOffsets (offsets : Merkle.Offsets) :
    toMerkleOffsets (fromMerkleOffsets offsets) = offsets := by
  cases offsets
  rfl

@[simp] theorem toMerkleOpening_fromMerkleOpening (opening : Merkle.Opening) :
    toMerkleOpening (fromMerkleOpening opening) = opening := by
  cases opening
  rfl

@[simp] theorem toMerkleIndices_fromMerkleIndices (indices : Merkle.Indices) :
    toMerkleIndices (fromMerkleIndices indices) = indices := by
  cases indices
  rfl

@[simp] theorem mapArray_opening_roundtrip
    (openings : Array Merkle.Opening 3#usize) :
    mapArray toMerkleOpening (mapArray fromMerkleOpening openings) =
      openings := by
  apply Subtype.ext
  simp only [mapArray, List.map_map]
  induction openings.val with
  | nil => rfl
  | cons opening rest ih =>
      simp only [List.map_cons, Function.comp_apply,
        toMerkleOpening_fromMerkleOpening, ih]

@[simp] theorem toMerkleVerified_fromMerkleVerified (verified : Merkle.Verified) :
    toMerkleVerified (fromMerkleVerified verified) = verified := by
  cases verified
  simp only [toMerkleVerified, fromMerkleVerified,
    toMerkleOpening_fromMerkleOpening, mapArray_opening_roundtrip,
    toMerkleIndices_fromMerkleIndices]

/-- Accepted-path model of the replay-only wrapper.  Successes and divergence
are preserved exactly and duplicate generated structs are converted field by
field.  All Merkle errors use one representative caller error because the
unchanged outer Rust caller maps every error variant to the same
`InvalidAccountData`; the accepted path cannot observe the discarded variant. -/
def exactMerkleOpeningCall
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash) :
    AspisV5FriCallerParametric.OpeningCall :=
  fun roots queries proof =>
    match V5MerkleUnchangedFull.private_openings.verify_v5_private_openings
        hash (toMerkleRoots roots) queries proof with
    | .fail error => .fail error
    | .div => .div
    | .ok (.Err _) => .ok (.Err (.InvalidSharedTopology))
    | .ok (.Ok verified) => .ok (.Ok (fromMerkleVerified verified))

/-- Exact successful-result equality between the first-order wrapper in the
caller extraction and the independently translated unchanged Merkle
function. It states only source/result equality, not authentication. -/
def AcceptedCallerMerkleSourceEquality
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash) :
    Prop :=
  ∀ roots queries proof verified,
    openingsCall roots queries proof = .ok (.Ok verified) →
      V5MerkleUnchangedFull.private_openings.verify_v5_private_openings
          hash (toMerkleRoots roots) queries proof =
        .ok (.Ok (toMerkleVerified verified))

/-- The explicit wrapper model discharges the successful-result source edge.
The remaining connection to Rust is the hash-pinned source/patch/extraction
replay described by this bundle, rather than an unproved mathematical fact. -/
theorem exactMerkleOpeningCall_sourceEquality
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash) :
    AcceptedCallerMerkleSourceEquality (exactMerkleOpeningCall hash) hash := by
  intro roots queries proof verified run
  unfold exactMerkleOpeningCall at run
  cases hverify :
      V5MerkleUnchangedFull.private_openings.verify_v5_private_openings
        hash (toMerkleRoots roots) queries proof with
  | fail error => simp [hverify] at run
  | div => simp [hverify] at run
  | ok result =>
      cases result with
      | Err error => simp [hverify] at run
      | Ok returned =>
          have returnedEq : fromMerkleVerified returned = verified := by
            simpa [hverify] using run
          subst verified
          simpa using hverify

@[simp] theorem toMerkleOpening_driver_view (opening : Caller.Opening) :
    AspisV5MerkleUnchangedFullSectionCallBridge.generatedOpeningToReturned
        (toMerkleOpening opening) =
      { count := opening.count.val
        valueWidth := opening.value_width.val
        records := opening.records.val.map
          AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte
        frontier := opening.frontier.val.map
          AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte
        offsets :=
          { count := opening.offsets.count.val
            records := opening.offsets.records.val
            frontierCount := opening.offsets.frontier_count.val
            frontier := opening.offsets.frontier.val
            endOffset := opening.offsets.end.val } } := by
  rfl

/-- A successful production caller trace, plus the exact one-call wrapper
edge, yields the same authenticated run and returned FRI view proved for the
unchanged Merkle verifier. In particular, the value which the caller passes
to FRI is not reconstructed from unauthenticated bytes. -/
theorem accepted_caller_opening_yields_exact_merkle_and_fri_view
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (modelQueries : Finset AspisV5MerkleAuthenticationBinding.V5Query)
    (queryCount : modelQueries.card = 18)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (prepareCall : AspisV5FriCallerParametric.PrepareCall)
    (friCall : AspisV5FriCallerParametric.FriCall)
    (parsed : AspisV5FriCallerParametric.Parsed)
    (queries : Array Std.U32 18#usize)
    (finalPolynomial : Array AspisV5FriCallerParametric.QM31 4#usize)
    (alphas : Array AspisV5FriCallerParametric.QM31 4#usize)
    (gamma : AspisV5FriCallerParametric.QM31)
    (output : AspisV5FriCallerParametric.QM31 ×
      AspisV5FriCallerParametric.Prepared)
    (trace : AspisV5FriCallerParametric.AcceptedCallerTrace openingsCall
      prepareCall friCall parsed queries finalPolynomial alphas gamma output)
    (hsource : AcceptedCallerMerkleSourceEquality openingsCall hash)
    (hhash : AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
      sha256 hash)
    (queryModel :
      (V5MerkleQueryReuseProof.expectedLayer0
          (Array.to_slice queries).val).map (fun index => index.val) =
        AspisV5TopologyConstruction.sharedLevelIndices modelQueries 0) :
    ∃ (rootsArray : Array
          AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedDigest
          5#usize)
      (modelRoots : AspisV5MerkleAuthenticationBinding.V5PrivateRoots
        AspisV5MerkleRustBridge.Digest32)
      (run : AspisV5MerkleRustBridge.ExactV5Run sha256 modelRoots modelQueries),
      (toMerkleRoots parsed.v5_private_roots).as_array = .ok rootsArray ∧
      AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedRootsMatch
        rootsArray modelRoots ∧
      run.proofBytes = parsed.v5_private_proof.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte ∧
      AspisV5FriConsumerObservationBridge.generatedDriverOutput
          (AspisV5MerkleFriReturnedOutputBridge.toFriVerified
            (toMerkleVerified trace.opening)) =
        AspisV5MerkleConsumedValueBridge.driverOutputOfRun run [] := by
  have hverify := hsource parsed.v5_private_roots (Array.to_slice queries)
    parsed.v5_private_proof trace.opening trace.opening_run
  obtain ⟨rootsArray, modelRoots, run, rootsEq, rootsMatch, proofEq,
      outputEq⟩ :=
    AspisV5MerkleUnchangedPublicAcceptanceBridge.generated_public_acceptance_yields_exact_v5_with_output
      sha256 modelQueries queryCount hash (toMerkleRoots parsed.v5_private_roots)
      (Array.to_slice queries) parsed.v5_private_proof
      (toMerkleVerified trace.opening) hhash queryModel hverify
  refine ⟨rootsArray, modelRoots, run, rootsEq, rootsMatch, proofEq, ?_⟩
  exact AspisV5MerkleFriReturnedOutputBridge.converted_driver_output_eq_run
    run (toMerkleVerified trace.opening) outputEq

/-- Accepted execution with the exact source-wrapper model yields an
authenticated Merkle run and the identical opening observed by FRI, without
an additional source-equality premise. -/
theorem accepted_exact_merkle_call_yields_authenticated_fri_view
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (modelQueries : Finset AspisV5MerkleAuthenticationBinding.V5Query)
    (queryCount : modelQueries.card = 18)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (prepareCall : AspisV5FriCallerParametric.PrepareCall)
    (friCall : AspisV5FriCallerParametric.FriCall)
    (parsed : AspisV5FriCallerParametric.Parsed)
    (queries : Array Std.U32 18#usize)
    (finalPolynomial : Array AspisV5FriCallerParametric.QM31 4#usize)
    (alphas : Array AspisV5FriCallerParametric.QM31 4#usize)
    (gamma : AspisV5FriCallerParametric.QM31)
    (output : AspisV5FriCallerParametric.QM31 ×
      AspisV5FriCallerParametric.Prepared)
    (trace : AspisV5FriCallerParametric.AcceptedCallerTrace
      (exactMerkleOpeningCall hash) prepareCall friCall parsed queries
      finalPolynomial alphas gamma output)
    (hhash : AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
      sha256 hash)
    (queryModel :
      (V5MerkleQueryReuseProof.expectedLayer0
          (Array.to_slice queries).val).map (fun index => index.val) =
        AspisV5TopologyConstruction.sharedLevelIndices modelQueries 0) :
    ∃ (rootsArray : Array
          AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedDigest
          5#usize)
      (modelRoots : AspisV5MerkleAuthenticationBinding.V5PrivateRoots
        AspisV5MerkleRustBridge.Digest32)
      (run : AspisV5MerkleRustBridge.ExactV5Run sha256 modelRoots modelQueries),
      (toMerkleRoots parsed.v5_private_roots).as_array = .ok rootsArray ∧
      AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedRootsMatch
        rootsArray modelRoots ∧
      run.proofBytes = parsed.v5_private_proof.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte ∧
      AspisV5FriConsumerObservationBridge.generatedDriverOutput
          (AspisV5MerkleFriReturnedOutputBridge.toFriVerified
            (toMerkleVerified trace.opening)) =
        AspisV5MerkleConsumedValueBridge.driverOutputOfRun run [] :=
  accepted_caller_opening_yields_exact_merkle_and_fri_view
    sha256 modelQueries queryCount hash (exactMerkleOpeningCall hash)
    prepareCall friCall parsed queries finalPolynomial alphas gamma output
    trace (exactMerkleOpeningCall_sourceEquality hash) hhash queryModel

#print axioms toMerkleOpening_driver_view
#print axioms exactMerkleOpeningCall_sourceEquality
#print axioms accepted_caller_opening_yields_exact_merkle_and_fri_view
#print axioms accepted_exact_merkle_call_yields_authenticated_fri_view

end AspisV5FriCallerMerkleBridge
