import V5AcceptedRelationSourceClosure

/-!
# Deterministic relation data from one accepted production snapshot

The accepted relation theorem formerly returned an existential four-round
projection.  This file fixes that projection once, retains the independently
recovered eight production tensor updates, and assembles the exact relation
tail consumed by the maintained source caller.  No claim table or main weight
schedule is supplied here; those are connected by their own source proofs.
-/

namespace AspisV5AcceptedDeterministicRelationTail

open Aeneas Aeneas.Std Result
open AspisV5AcceptedRelationRoundInversion
open AspisV5AcceptedRelationRoundProjection
open AspisV5AcceptedRelationPreparedAdapter
open AspisV5AcceptedRelationSourceClosure
open AspisV5AcceptedSameRunRelationFriSnapshot
open AspisV5RelationStressSourceBridge
open AspisV5ComponentCPreProjectionDeployed
open AspisV5CompactTerminalOptimized

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev K := AspisV5FriAcceptedForestChecks.K

deriving instance Inhabited for
  V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint

/-- The accepted execution and its scalar projection selected together.  The
combined witness retains the exact eight decoder outputs used by both views. -/
noncomputable def acceptedSnapshotRoundEvidence
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    AcceptedFourRoundExecutionProjections snapshot.relationTrace :=
  Classical.choice
    (accepted_full_trace_exposes_four_execution_projections
      snapshot.relationTrace
      (accepted_snapshot_initial_relation_is_canonical snapshot)
      (accepted_snapshot_relation_alphas_are_canonical snapshot))

/-- The deterministic maintained scalar projection of the combined accepted
witness. -/
noncomputable def acceptedSnapshotRounds
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    AcceptedFourRawRoundProjections snapshot.relationTrace :=
  (acceptedSnapshotRoundEvidence snapshot).projections

/-- The deterministic projection inherits the already-proved successful
maintained four-round execution. -/
theorem acceptedSnapshotRounds_run
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    runSourceRelationVerifier
        (acceptedSourceRelationInput (acceptedSnapshotRounds snapshot)) =
      some {
        finalCoefficients := fun index =>
          toField snapshot.relationTrace.finalCoefficients.val[index.val]!
        terminalClaim := toField snapshot.relationTrace.claim4 } :=
  by
    have initialLog :=
      AspisV5RelationPrepareLogLenProof.Prepare.prepareSuccess_implies_weights_log_len
        (AspisV5AcceptedRelationPreparedAdapter.parsedToCaller parsed)
        (AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller
          snapshot.verifiedPrefix.kappa)
        (AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller
          snapshot.verifiedPrefix.inactive_claim)
        (AspisV5AcceptedRelationPreparedAdapter.preparedClaimsToCaller
          snapshot.preparedClaims)
        snapshot.relationTrace.calls.relation
        snapshot.relationTrace.calls.ignoredAlphas
        snapshot.relationTrace.calls.denseScale
        snapshot.relationTrace.calls.prepareSuccess
    have terminalExact :=
      AspisV5RelationTerminalDotCanonical.accepted_trace_terminal_add_exact_of_initial
        snapshot.relationTrace initialLog
        (accepted_snapshot_final_coefficients_are_canonical snapshot)
    exact accepted_trace_runs_source_relation_verifier
      (acceptedSnapshotRounds snapshot) terminalExact

/-- The exact four-round production control-flow evidence selected once from
the accepted trace.  Its eight sample records retain the actual tensor calls
and their returned accumulators. -/
noncomputable def acceptedSnapshotExecutions
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    AcceptedFourRoundExecution snapshot.relationTrace :=
  (acceptedSnapshotRoundEvidence snapshot).execution

/-- Select one of the four maintained round records without introducing a
free round schedule. -/
noncomputable def acceptedProjectedRound
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (round : Fin 4) : SourceRelationRound K :=
  let rounds := acceptedSnapshotRounds snapshot
  if round = 0 then projectedRound rounds.round0.raw
  else if round = 1 then projectedRound rounds.round1.raw
  else if round = 2 then projectedRound rounds.round2.raw
  else projectedRound rounds.round3.raw

@[simp] theorem acceptedProjectedRound_zero
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    acceptedProjectedRound snapshot 0 =
      projectedRound (acceptedSnapshotRounds snapshot).round0.raw := by
  simp [acceptedProjectedRound]

@[simp] theorem acceptedProjectedRound_one
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    acceptedProjectedRound snapshot 1 =
      projectedRound (acceptedSnapshotRounds snapshot).round1.raw := by
  simp [acceptedProjectedRound, Fin.ext_iff]

@[simp] theorem acceptedProjectedRound_two
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    acceptedProjectedRound snapshot 2 =
      projectedRound (acceptedSnapshotRounds snapshot).round2.raw := by
  simp [acceptedProjectedRound, Fin.ext_iff]

@[simp] theorem acceptedProjectedRound_three
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    acceptedProjectedRound snapshot 3 =
      projectedRound (acceptedSnapshotRounds snapshot).round3.raw := by
  simp [acceptedProjectedRound, Fin.ext_iff]

/-- The four circle coordinates are the exact two `(x,y)` points decoded by
the accepted production outer loop, in their physical byte order. -/
def acceptedCircleCoordinate
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (coordinate : Fin 4) : K :=
  if coordinate = 0 then toField snapshot.relationTrace.circlePoints.val[0]!.x
  else if coordinate = 1 then
    toField snapshot.relationTrace.circlePoints.val[0]!.y
  else if coordinate = 2 then
    toField snapshot.relationTrace.circlePoints.val[1]!.x
  else toField snapshot.relationTrace.circlePoints.val[1]!.y

/-- The decoded line value retained by one accepted nonzero-round tensor
update.  Both existential witnesses come from the exact decoder/tensor call
stored in that update record. -/
noncomputable def acceptedLineValue
    {bytes : Array Std.U8 928#usize}
    {circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize}
    {round sample : Std.Usize}
    {mix : AspisV5AcceptedRelationRoundInversion.RawQM31}
    {weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator}
    (update : AcceptedSampleWeightUpdate bytes circlePoints round sample mix
      weights nextWeights)
    (nonzero : round ≠ 0#usize) :
    AspisV5AcceptedRelationRoundInversion.RawQM31 :=
  Classical.choose (Classical.choose_spec (update.line nonzero))

/-- The six line coordinates are the exact decoded values used by the two
production tensor additions in rounds one, two, and three. -/
noncomputable def acceptedLinePoint
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (point : Fin 6) : K :=
  let rounds := acceptedSnapshotExecutions snapshot
  if point = 0 then
    toField (acceptedLineValue rounds.round1.sample0WeightUpdate (by decide))
  else if point = 1 then
    toField (acceptedLineValue rounds.round1.sample1WeightUpdate (by decide))
  else if point = 2 then
    toField (acceptedLineValue rounds.round2.sample0WeightUpdate (by decide))
  else if point = 3 then
    toField (acceptedLineValue rounds.round2.sample1WeightUpdate (by decide))
  else if point = 4 then
    toField (acceptedLineValue rounds.round3.sample0WeightUpdate (by decide))
  else
    toField (acceptedLineValue rounds.round3.sample1WeightUpdate (by decide))

/-- The complete 58-field relation record fixed by one accepted execution.
The fields consumed by the scalar verifier come from the deterministic raw
rounds; circle and line fields come from the exact accepted tensor-update
execution; final coefficients come from the accepted public polynomial. -/
noncomputable def acceptedSnapshotRelationTail
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    PhysicalRelationFields K where
  circlePointCoordinates := acceptedCircleCoordinate snapshot
  linePoints := acceptedLinePoint snapshot
  oodValues := fun round sample =>
    if sample = 0 then (acceptedProjectedRound snapshot round).firstValue
    else (acceptedProjectedRound snapshot round).secondValue
  oodMixes := fun round sample =>
    if sample = 0 then (acceptedProjectedRound snapshot round).firstMix
    else (acceptedProjectedRound snapshot round).secondMix
  polynomialCoefficients := fun round =>
    (acceptedProjectedRound snapshot round).polynomial
  finalCoefficients := snapshotPublishedFinal snapshot

@[simp] theorem acceptedSnapshotRelationTail_ood_zero
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (round : Fin 4) :
    (acceptedSnapshotRelationTail snapshot).oodValues round 0 =
      (acceptedProjectedRound snapshot round).firstValue := by
  simp [acceptedSnapshotRelationTail]

@[simp] theorem acceptedSnapshotRelationTail_ood_one
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (round : Fin 4) :
    (acceptedSnapshotRelationTail snapshot).oodValues round 1 =
      (acceptedProjectedRound snapshot round).secondValue := by
  change (if (1 : Fin 2) = 0 then
      (acceptedProjectedRound snapshot round).firstValue
    else (acceptedProjectedRound snapshot round).secondValue) =
      (acceptedProjectedRound snapshot round).secondValue
  rw [if_neg (by decide)]

@[simp] theorem acceptedSnapshotRelationTail_mix_zero
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (round : Fin 4) :
    (acceptedSnapshotRelationTail snapshot).oodMixes round 0 =
      (acceptedProjectedRound snapshot round).firstMix := by
  simp [acceptedSnapshotRelationTail]

@[simp] theorem acceptedSnapshotRelationTail_mix_one
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (round : Fin 4) :
    (acceptedSnapshotRelationTail snapshot).oodMixes round 1 =
      (acceptedProjectedRound snapshot round).secondMix := by
  change (if (1 : Fin 2) = 0 then
      (acceptedProjectedRound snapshot round).firstMix
    else (acceptedProjectedRound snapshot round).secondMix) =
      (acceptedProjectedRound snapshot round).secondMix
  rw [if_neg (by decide)]

@[simp] theorem acceptedSnapshotRelationTail_polynomial
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (round : Fin 4) :
    (acceptedSnapshotRelationTail snapshot).polynomialCoefficients round =
      (acceptedProjectedRound snapshot round).polynomial := by
  rfl

@[simp] theorem acceptedSnapshotRelationTail_final
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    (acceptedSnapshotRelationTail snapshot).finalCoefficients =
      snapshotPublishedFinal snapshot := by
  rfl

/-- Partial caller data with every accepted relation-tail field fixed.  Only
the independently decoded 76-entry claim table and the actual production
main-weight schedule remain parameters at this layer. -/
noncomputable def acceptedSnapshotPartialCallerData
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → K)
    (mainWeights : SourceMainWeightSchedule K) :
    SourceMode9CallerData K :=
  snapshotCallerData snapshot pointMajorClaims
    (acceptedSnapshotRelationTail snapshot) mainWeights

@[simp] theorem acceptedSnapshotPartialCallerData_inactiveClaim
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → K)
    (mainWeights : SourceMainWeightSchedule K) :
    (acceptedSnapshotPartialCallerData snapshot pointMajorClaims mainWeights).inactiveClaim =
      entryToK snapshot.verifiedPrefix.inactive_claim := by
  rfl

@[simp] theorem acceptedSnapshotPartialCallerData_kappa
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → K)
    (mainWeights : SourceMainWeightSchedule K) :
    (acceptedSnapshotPartialCallerData snapshot pointMajorClaims mainWeights).kappa =
      entryToK snapshot.verifiedPrefix.kappa := by
  rfl

@[simp] theorem acceptedSnapshotPartialCallerData_gamma
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → K)
    (mainWeights : SourceMainWeightSchedule K) :
    (acceptedSnapshotPartialCallerData snapshot pointMajorClaims mainWeights).gamma =
      entryToK snapshot.verifiedPrefix.gamma := by
  rfl

@[simp] theorem acceptedSnapshotPartialCallerData_pointMajorClaims
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → K)
    (mainWeights : SourceMainWeightSchedule K) :
    (acceptedSnapshotPartialCallerData snapshot pointMajorClaims mainWeights).pointMajorClaims =
      pointMajorClaims := by
  rfl

@[simp] theorem acceptedSnapshotPartialCallerData_finalCoefficients
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → K)
    (mainWeights : SourceMainWeightSchedule K) :
    (acceptedSnapshotPartialCallerData snapshot pointMajorClaims mainWeights).relationTail.finalCoefficients =
      snapshotPublishedFinal snapshot := by
  rfl

@[simp] theorem acceptedSnapshotPartialCallerData_alphas
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → K)
    (mainWeights : SourceMainWeightSchedule K) :
    (acceptedSnapshotPartialCallerData snapshot pointMajorClaims mainWeights).alphas =
      fun layer => entryToK snapshot.alphas.val[layer.val]! := by
  rfl

@[simp] theorem acceptedSnapshotPartialCallerData_mainWeights
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → K)
    (mainWeights : SourceMainWeightSchedule K) :
    (acceptedSnapshotPartialCallerData snapshot pointMajorClaims mainWeights).mainWeights =
      mainWeights := by
  rfl

@[simp] theorem acceptedSnapshotPartialCallerData_componentBPoint
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → K)
    (mainWeights : SourceMainWeightSchedule K) :
    (acceptedSnapshotPartialCallerData snapshot pointMajorClaims mainWeights).componentBPoint =
      fun coordinate =>
        entryToK snapshot.verifiedPrefix.round_challenges.val[coordinate.val]! := by
  rfl

/-- A dependent fixed array's in-bounds list lookup agrees with its total
`get!` lookup.  Keeping this conversion explicit avoids relying on proof-term
normalization for generated `Std.Usize` lengths. -/
private theorem fixedArray_getBang_eq_get
    {T : Type} [Inhabited T] {count : Std.Usize}
    (values : Array T count) (index : Fin count.val) :
    values.val[index.val]! = values.val[index.val] := by
  have lengthExact : values.val.length = count.val := Array.length_eq values
  have inBounds : index.val < values.val.length := by
    simpa only [lengthExact] using index.isLt
  apply List.getElem!_of_getElem?
  simp [inBounds]

/-- The accepted entry alpha and the alpha retained by the deterministic raw
round are the same exact field element. -/
theorem acceptedSnapshot_alpha_eq_projected
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (round : Fin 4) :
    entryToK snapshot.alphas.val[round.val]! =
      (acceptedProjectedRound snapshot round).alpha := by
  let rounds := acceptedSnapshotRounds snapshot
  fin_cases round
  · change entryToK snapshot.alphas.val[0]! =
      toField rounds.round0.raw.alpha
    rw [rounds.round0.alphaExact]
    rw [entryToK_eq_relationCallerValue]
    unfold acceptedAlphaAt
    rw [qm31ArrayToCaller_get]
    unfold toField
    exact congrArg
      (fun value =>
        AspisV5RelationLinkedFieldProjection.toMaintainedExact
          (AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller value))
      (fixedArray_getBang_eq_get snapshot.alphas ⟨0, by decide⟩)
  · change entryToK snapshot.alphas.val[1]! =
      toField rounds.round1.raw.alpha
    rw [rounds.round1.alphaExact]
    rw [entryToK_eq_relationCallerValue]
    unfold acceptedAlphaAt
    rw [qm31ArrayToCaller_get]
    unfold toField
    exact congrArg
      (fun value =>
        AspisV5RelationLinkedFieldProjection.toMaintainedExact
          (AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller value))
      (fixedArray_getBang_eq_get snapshot.alphas ⟨1, by decide⟩)
  · change entryToK snapshot.alphas.val[2]! =
      toField rounds.round2.raw.alpha
    rw [rounds.round2.alphaExact]
    rw [entryToK_eq_relationCallerValue]
    unfold acceptedAlphaAt
    rw [qm31ArrayToCaller_get]
    unfold toField
    exact congrArg
      (fun value =>
        AspisV5RelationLinkedFieldProjection.toMaintainedExact
          (AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller value))
      (fixedArray_getBang_eq_get snapshot.alphas ⟨2, by decide⟩)
  · change entryToK snapshot.alphas.val[3]! =
      toField rounds.round3.raw.alpha
    rw [rounds.round3.alphaExact]
    rw [entryToK_eq_relationCallerValue]
    unfold acceptedAlphaAt
    rw [qm31ArrayToCaller_get]
    unfold toField
    exact congrArg
      (fun value =>
        AspisV5RelationLinkedFieldProjection.toMaintainedExact
          (AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller value))
      (fixedArray_getBang_eq_get snapshot.alphas ⟨3, by decide⟩)

/-- Every round assembled by the partial caller is exactly the deterministic
round projected from the accepted translated execution. -/
theorem acceptedSnapshotPartialCallerData_round
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → K)
    (mainWeights : SourceMainWeightSchedule K)
    (round : Fin 4) :
    sourceCallerRound
        (acceptedSnapshotPartialCallerData snapshot pointMajorClaims mainWeights)
        round = acceptedProjectedRound snapshot round := by
  change ({
    firstValue := (acceptedProjectedRound snapshot round).firstValue
    secondValue := (acceptedProjectedRound snapshot round).secondValue
    firstMix := (acceptedProjectedRound snapshot round).firstMix
    secondMix := (acceptedProjectedRound snapshot round).secondMix
    polynomial := (acceptedProjectedRound snapshot round).polynomial
    alpha := entryToK snapshot.alphas.val[round.val]!
  } : SourceRelationRound K) = acceptedProjectedRound snapshot round
  rw [acceptedSnapshot_alpha_eq_projected snapshot round]

/-- The public final polynomial retained by the snapshot is exactly the
array returned by the accepted production relation verifier. -/
theorem snapshotPublishedFinal_eq_relationTrace
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    snapshotPublishedFinal snapshot = fun index =>
      toField snapshot.relationTrace.finalCoefficients.val[index.val]! := by
  funext index
  have finalMatch := snapshot.relationTrace.calls.finalPolynomialMatch
  rw [snapshot.relationTrace.outputExact] at finalMatch
  have elementMatch := congrArg
    (fun (values : Array V5RelationCallerGenerated.aspis_core.field.QM31
      4#usize) => values.val[index.val]!) finalMatch
  change entryToK snapshot.finalPolynomial.val[index.val]! = _
  rw [elementMatch]
  rw [entryToK_eq_relationCallerValue]
  rw [qm31ArrayToCaller_get_bang]
  rfl

/-- The compact-dot premise needed by the complete deterministic relation
input is derived from the accepted production execution itself.  In
particular, the production constructor scale is rewritten to the exact
accepted `kappa³`, rather than supplied as an external equality. -/
theorem accepted_snapshot_compact_dot_exact
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    optimizedCompactFinalDot
        (fun coordinate =>
          entryToK snapshot.verifiedPrefix.round_challenges.val[
            coordinate.val]!)
        ((entryToK snapshot.verifiedPrefix.kappa) ^ 3)
        (fun layer => entryToK snapshot.alphas.val[layer.val]!)
        (snapshotPublishedFinal snapshot) =
      toField snapshot.relationTrace.additiveDot := by
  have compact := accepted_snapshot_compact_terminal_exact snapshot
  have pointExact :
      (fun coordinate : Fin 10 =>
        entryToK snapshot.verifiedPrefix.round_challenges.val[
          coordinate.val]!) =
      (fun coordinate : Fin 10 =>
        AspisV5RelationGeneratedFieldProjection.toMaintainedExact
          (qm31ArrayToCaller
            snapshot.verifiedPrefix.round_challenges).val[coordinate.val]!) := by
    funext coordinate
    rw [entryToK_eq_relationCallerValue, qm31ArrayToCaller_get_bang]
    rfl
  have scaleExact : (entryToK snapshot.verifiedPrefix.kappa) ^ 3 =
      AspisV5RelationGeneratedFieldProjection.toMaintainedExact
        snapshot.relationTrace.calls.denseScale := by
    rw [entryToK_eq_relationCallerValue]
    exact (accepted_snapshot_dense_scale_is_kappa_cube snapshot).symm
  have alphaExact :
      (fun layer : Fin 4 => entryToK snapshot.alphas.val[layer.val]!) =
      (fun layer : Fin 4 =>
        AspisV5RelationGeneratedFieldProjection.toMaintainedExact
          (acceptedAlphaAt (qm31ArrayToCaller snapshot.alphas) layer)) := by
    funext layer
    rw [entryToK_eq_relationCallerValue]
    unfold acceptedAlphaAt
    rw [fixedArray_getBang_eq_get snapshot.alphas layer]
    rw [qm31ArrayToCaller_get]
    rfl
  have finalExact : snapshotPublishedFinal snapshot =
      (fun index : Fin 4 =>
        AspisV5RelationGeneratedFieldProjection.toMaintainedExact
          snapshot.relationTrace.finalCoefficients.val[index.val]!) := by
    simpa [toField] using snapshotPublishedFinal_eq_relationTrace snapshot
  rw [pointExact, scaleExact, alphaExact, finalExact]
  exact compact.2.symm

/-- Once the independently proved initial-claim, main-dot, and compact-dot
equalities are supplied, all remaining fields of the complete source caller
input are definitionally the exact accepted source relation input. -/
theorem acceptedSnapshotPartialCallerData_relationInput_exact
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (pointMajorClaims : Fin 76 → K)
    (mainWeights : SourceMainWeightSchedule K)
    (initialExact :
      sourceCallerInitialClaim
          (entryToK snapshot.verifiedPrefix.inactive_claim)
          (entryToK snapshot.verifiedPrefix.kappa)
          (entryToK snapshot.verifiedPrefix.gamma) pointMajorClaims =
        toField snapshot.relationTrace.calls.relation.relation_value)
    (mainDotExact :
      sourceMainFinalDot mainWeights
          (sourceCallerChallenges
            (acceptedSnapshotPartialCallerData snapshot pointMajorClaims
              mainWeights))
          (snapshotPublishedFinal snapshot) =
        toField snapshot.relationTrace.mainDot)
    (additiveDotExact :
      optimizedCompactFinalDot
          (fun coordinate =>
            entryToK snapshot.verifiedPrefix.round_challenges.val[
              coordinate.val]!)
          ((entryToK snapshot.verifiedPrefix.kappa) ^ 3)
          (fun layer => entryToK snapshot.alphas.val[layer.val]!)
          (snapshotPublishedFinal snapshot) =
        toField snapshot.relationTrace.additiveDot) :
    sourceMode9RelationInput
        (acceptedSnapshotPartialCallerData snapshot pointMajorClaims
          mainWeights) =
      acceptedSourceRelationInput (acceptedSnapshotRounds snapshot) := by
  unfold sourceMode9RelationInput
  simp only [acceptedSnapshotPartialCallerData_inactiveClaim,
    acceptedSnapshotPartialCallerData_kappa,
    acceptedSnapshotPartialCallerData_gamma,
    acceptedSnapshotPartialCallerData_pointMajorClaims,
    acceptedSnapshotPartialCallerData_finalCoefficients,
    acceptedSnapshotPartialCallerData_alphas,
    acceptedSnapshotPartialCallerData_mainWeights,
    acceptedSnapshotPartialCallerData_componentBPoint]
  rw [initialExact,
    acceptedSnapshotPartialCallerData_round snapshot pointMajorClaims
      mainWeights 0,
    acceptedSnapshotPartialCallerData_round snapshot pointMajorClaims
      mainWeights 1,
    acceptedSnapshotPartialCallerData_round snapshot pointMajorClaims
      mainWeights 2,
    acceptedSnapshotPartialCallerData_round snapshot pointMajorClaims
      mainWeights 3,
    mainDotExact, additiveDotExact,
    snapshotPublishedFinal_eq_relationTrace snapshot]
  rfl

#print axioms acceptedSnapshotRounds_run
#print axioms accepted_snapshot_compact_dot_exact
#print axioms acceptedSnapshotPartialCallerData_relationInput_exact

end AspisV5AcceptedDeterministicRelationTail
