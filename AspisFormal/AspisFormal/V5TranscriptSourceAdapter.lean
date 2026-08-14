import AspisFormal.V5TranscriptConnection

/-!
# Source-shaped V5 transcript adapter

This file separates the remaining production-source question from the already
proved transcript model.  It does two concrete things:

* projects every transcript byte field from an arbitrary repaired runtime body
  at the offsets used by `parse_probe_data`; and
* gives a small, explicit, three-segment driver mirroring
  `verify_v5_wire_prefix`, `replay_real_v5_relation_rounds`, and
  `derive_v5_complete_queries_for_selector_from_transcript`.

The adapter is deliberately independent of SHA-256 security.  Hash calls and
sampler success determine the supplied `V5DerivedValues`; this file proves the
byte/event order and the exact values handed to the FRI and relation phases.

This is not presented as Charon/Aeneas extraction of the three production
functions.  The final source-to-adapter connection remains a separately named
boundary, rather than being hidden as an assumption that the complete Rust
driver equals the complete Lean driver.
-/

namespace AspisV5TranscriptSourceAdapter

open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5NonceWorkAuthentication
open AspisV5TranscriptConnection

/-! ## Fixed-body projection -/

/-- Read an exact fixed-width field from the repaired portion of a runtime
body.  The proof argument says only that the field ends before the fixed-body
boundary; it does not assume a particular private-opening suffix size. -/
def fixedBodyField (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (start width : Nat) (hstop : start + width ≤ repairedFixedBytes) :
    FixedBytes width :=
  fun index =>
    runtimeWireByteAt shape wire
      ⟨start + index.val, by
        have hlocal := index.isLt
        simp only [runtimeRepairedProofBytes]
        omega⟩

def prefixBodyField (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (relativeStart width : Nat)
    (hstop : wirePrefixOffset + relativeStart + width ≤ repairedFixedBytes) :
    FixedBytes width :=
  fixedBodyField shape wire (wirePrefixOffset + relativeStart) width (by omega)

def stressBodyField (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (relativeStart width : Nat)
    (hstop : relationStressOffset + relativeStart + width ≤ repairedFixedBytes) :
    FixedBytes width :=
  fixedBodyField shape wire (relationStressOffset + relativeStart) width (by omega)

/-! The following literal relative offsets are the compile-time-asserted Rust
values in `v5_cu_probe.rs` and `v5_relation_stress.rs`. -/

def prefixInitialClaimOffset : Nat := 87
def prefixSemanticSumcheckOffset : Nat := 103
def prefixTerminalClaimsOffset : Nat := 5799
def prefixInactiveClaimOffset : Nat := 5847
def prefixPublicSaltsOffset : Nat := 5863

def stressOodOffset : Nat := 160
def stressSumcheckOffset : Nat := 416

def privateCircleRootOffset (layer : Fin 4) : Nat :=
  if layer.val = 0 then privateRootsOffset
  else privateRootsOffset + 32 * (layer.val + 1)

def fixedBodyPublicSalt (shape : RuntimeShape)
    (wire : RuntimeExactWire shape) (saltSection : Fin 5) : FixedBytes 32 :=
  prefixBodyField shape wire
    (prefixPublicSaltsOffset + 32 * saltSection.val) 32 (by
      have hsection := saltSection.isLt
      norm_num [wirePrefixOffset, prefixPublicSaltsOffset, repairedFixedBytes]
      omega)

def fixedBodyCircleRoot (shape : RuntimeShape)
    (wire : RuntimeExactWire shape) (layer : Fin 4) : FixedBytes 32 :=
  fixedBodyField shape wire (privateCircleRootOffset layer) 32 (by
    have hlayer := layer.isLt
    simp only [privateCircleRootOffset]
    split
    all_goals norm_num [privateRootsOffset, repairedFixedBytes]
    all_goals omega)

/-- Byte-for-byte transcript input projection from the repaired body.  Work
values are the six values supplied by the already source-extracted work-wire
projection; `workProjection` below ties them back to the same body bytes. -/
def decodedTranscriptInput (shape : RuntimeShape)
    (wire : RuntimeExactWire shape) (statementDigest : FixedBytes 32)
    (work : WorkWireView) : V5TranscriptInputs where
  statementDigest := statementDigest
  circleRoot := fixedBodyCircleRoot shape wire
  c2Root := fixedBodyField shape wire (privateRootsOffset + 32) 32 (by
    norm_num [privateRootsOffset, repairedFixedBytes])
  publicSalt := fixedBodyPublicSalt shape wire
  initialClaim := prefixBodyField shape wire prefixInitialClaimOffset 16 (by
    norm_num [wirePrefixOffset, prefixInitialClaimOffset, repairedFixedBytes])
  semanticSumcheck := fun round =>
    prefixBodyField shape wire
      (prefixSemanticSumcheckOffset + 448 * round.val) 448 (by
        have hround := round.isLt
        norm_num [wirePrefixOffset, prefixSemanticSumcheckOffset,
          repairedFixedBytes]
        omega)
  relationPoints := fixedBodyField shape wire relationPointsOffset 480 (by
    norm_num [relationPointsOffset, repairedFixedBytes])
  statementEvaluations :=
    fixedBodyField shape wire relationClaimsOffset 1216 (by
      norm_num [relationClaimsOffset, repairedFixedBytes])
  terminalClaims := prefixBodyField shape wire prefixTerminalClaimsOffset 48 (by
    norm_num [wirePrefixOffset, prefixTerminalClaimsOffset, repairedFixedBytes])
  batchNonce := work.nonces .batch
  inactiveClaim := prefixBodyField shape wire prefixInactiveClaimOffset 16 (by
    norm_num [wirePrefixOffset, prefixInactiveClaimOffset, repairedFixedBytes])
  oodValue := fun round sample =>
    stressBodyField shape wire
      (stressOodOffset + 16 * (2 * round.val + sample.val)) 16 (by
        have hround := round.isLt
        have hsample := sample.isLt
        norm_num [relationStressOffset, stressOodOffset, repairedFixedBytes]
        omega)
  relationSumcheck := fun round =>
    stressBodyField shape wire
      (stressSumcheckOffset + 112 * round.val) 112 (by
        have hround := round.isLt
        norm_num [relationStressOffset, stressSumcheckOffset, repairedFixedBytes]
        omega)
  foldNonce := fun round => work.nonces (.fold round)
  finalPolynomial := fixedBodyField shape wire finalCoefficientsOffset 64 (by
    norm_num [finalCoefficientsOffset, repairedFixedBytes])
  finalNonce := work.nonces .finalQuery
  selector := fixedBodyField shape wire querySelectorOffset 1 (by
    norm_num [querySelectorOffset, repairedFixedBytes]) 0

theorem decoded_input_uses_exact_work_projection
    (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (statementDigest : FixedBytes 32) (work : WorkWireView)
    (hwork : ExactWorkWireProjection shape wire work) :
    (decodedTranscriptInput shape wire statementDigest work).nonce = work.nonces ∧
      (∀ kind,
        (projectWorkWire shape wire).noncePayload kind =
          nonceLEBytes ((decodedTranscriptInput shape wire statementDigest work).nonce kind)) := by
  constructor
  · funext kind
    cases kind <;> rfl
  · intro kind
    have hpayload := congrArg (fun projection => projection.noncePayload kind) hwork
    have hnonce :
        (decodedTranscriptInput shape wire statementDigest work).nonce kind =
          work.nonces kind := by
      cases kind <;> rfl
    rw [hnonce]
    simpa [canonicalWorkWire] using hpayload

theorem decoded_selector_is_exact_global_byte
    (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (statementDigest : FixedBytes 32) (work : WorkWireView) :
    (decodedTranscriptInput shape wire statementDigest work).selector =
      runtimeWireByteAt shape wire
        ⟨querySelectorOffset, by
          simp only [runtimeRepairedProofBytes]
          norm_num [querySelectorOffset, repairedFixedBytes]
          omega⟩ := by
  simp [decodedTranscriptInput, fixedBodyField]

theorem decoded_relation_and_fri_fields_are_exact_body_slices
    (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (statementDigest : FixedBytes 32) (work : WorkWireView) :
    let input := decodedTranscriptInput shape wire statementDigest work
    input.relationPoints =
        fixedBodyField shape wire relationPointsOffset 480 (by
          norm_num [relationPointsOffset, repairedFixedBytes]) ∧
      input.statementEvaluations =
        fixedBodyField shape wire relationClaimsOffset 1216 (by
          norm_num [relationClaimsOffset, repairedFixedBytes]) ∧
      input.finalPolynomial =
        fixedBodyField shape wire finalCoefficientsOffset 64 (by
          norm_num [finalCoefficientsOffset, repairedFixedBytes]) := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Explicit source segments -/

def sourceAbsorb (input : V5TranscriptInputs) (slot : AbsorbSlot) :
    TranscriptEvent :=
  .absorb slot slot.label (absorbPayload input slot)

def sourceSqueeze (slot : SqueezeSlot) : TranscriptEvent :=
  .squeeze slot

def sourceCheckAndAbsorb
    (input : V5TranscriptInputs) (kind : WorkKind) : List TranscriptEvent :=
  [.verifyWork kind kind.difficulty
      (List.ofFn (nonceLEBytes (input.nonce kind))),
    sourceAbsorb input (workAbsorbSlot kind)]

def sourceSemanticRound
    (input : V5TranscriptInputs) (round : Fin 10) : List TranscriptEvent :=
  [sourceAbsorb input (.semanticSumcheck round),
    sourceSqueeze (.relationChallenge round)]

/-- Direct event form of successful `verify_v5_wire_prefix`. -/
def sourcePrefix (input : V5TranscriptInputs) : List TranscriptEvent :=
  [sourceAbsorb input .profile,
    sourceAbsorb input .basis,
    sourceAbsorb input .statement,
    sourceAbsorb input (.circleRoot 0),
    sourceSqueeze .lambda,
    sourceSqueeze .chi,
    sourceAbsorb input .c2Root,
    sourceAbsorb input .constraintRegistry,
    sourceAbsorb input .helperSum,
    sourceSqueeze .theta] ++
  List.ofFn (fun coordinate : Fin 10 =>
    sourceSqueeze (.zerocheckPoint coordinate)) ++
  [sourceSqueeze .mu,
    sourceAbsorb input .maskClaim,
    sourceSqueeze .eta] ++
  (List.ofFn (sourceSemanticRound input)).flatten ++
  [sourceAbsorb input .relationPoints,
    sourceAbsorb input .statementEvaluations,
    sourceAbsorb input .terminalClaims] ++
  sourceCheckAndAbsorb input .batch ++
  [sourceSqueeze .gamma,
    sourceAbsorb input .inactiveClaim,
    sourceSqueeze .kappa]

def sourceOodSample (input : V5TranscriptInputs)
    (round : Fin 4) (sample : Fin 2) : List TranscriptEvent :=
  [sourceSqueeze (.oodPoint round sample),
    sourceAbsorb input (.oodValue round sample),
    sourceSqueeze (.oodMix round sample)]

def sourceLaterRoot (input : V5TranscriptInputs)
    (round : Fin 4) : List TranscriptEvent :=
  match laterLayer round with
  | none => []
  | some layer => [sourceAbsorb input (.circleRoot layer)]

def sourceRelationRound (input : V5TranscriptInputs)
    (round : Fin 4) : List TranscriptEvent :=
  sourceOodSample input round 0 ++
    sourceOodSample input round 1 ++
    [sourceAbsorb input (.relationSumcheck round)] ++
    sourceCheckAndAbsorb input (.fold round) ++
    [sourceSqueeze (.foldChallenge round)] ++
    sourceLaterRoot input round

/-- Direct event form of successful `replay_real_v5_relation_rounds`. -/
def sourceRelation (input : V5TranscriptInputs) : List TranscriptEvent :=
  (List.ofFn (sourceRelationRound input)).flatten

/-- Direct event form of successful
`derive_v5_complete_queries_for_selector_from_transcript`. -/
def sourceTail (input : V5TranscriptInputs) : List TranscriptEvent :=
  [sourceAbsorb input .finalPolynomial] ++
    sourceCheckAndAbsorb input .finalQuery ++
    [sourceAbsorb input .selector, sourceSqueeze .queries]

theorem source_absorb_is_realized_step
    (input : V5TranscriptInputs) (slot : AbsorbSlot) :
    sourceAbsorb input slot = realizeStep input (.absorb slot) := by
  rfl

theorem source_squeeze_is_realized_step
    (input : V5TranscriptInputs) (slot : SqueezeSlot) :
    sourceSqueeze slot = realizeStep input (.squeeze slot) := by
  rfl

theorem source_check_and_absorb_is_exact
    (input : V5TranscriptInputs) (kind : WorkKind) :
    sourceCheckAndAbsorb input kind =
      (workSchedule kind).map (realizeStep input) := by
  rfl

theorem source_semantic_round_is_exact
    (input : V5TranscriptInputs) (round : Fin 10) :
    sourceSemanticRound input round =
      (semanticRoundSchedule round).map (realizeStep input) := by
  rfl

theorem source_ood_sample_is_exact
    (input : V5TranscriptInputs) (round : Fin 4) (sample : Fin 2) :
    sourceOodSample input round sample =
      (oodSampleSchedule round sample).map (realizeStep input) := by
  rfl

theorem source_later_root_is_exact
    (input : V5TranscriptInputs) (round : Fin 4) :
    sourceLaterRoot input round =
      (laterLayer round).toList.map
        (fun layer => realizeStep input (.absorb (.circleRoot layer))) := by
  cases h : laterLayer round <;>
    simp [sourceLaterRoot, h, sourceAbsorb, realizeStep]

theorem source_relation_round_is_exact
    (input : V5TranscriptInputs) (round : Fin 4) :
    sourceRelationRound input round =
      (relationRoundSchedule round).map (realizeStep input) := by
  simp [sourceRelationRound, relationRoundSchedule, source_ood_sample_is_exact,
    source_check_and_absorb_is_exact, source_later_root_is_exact,
    List.map_append, sourceAbsorb, sourceSqueeze, realizeStep]

theorem source_prefix_is_exact (input : V5TranscriptInputs) :
    sourcePrefix input = prefixSchedule.map (realizeStep input) := by
  simp [sourcePrefix, prefixSchedule, sourceSemanticRound,
    sourceCheckAndAbsorb, workSchedule, semanticRoundSchedule, sourceAbsorb,
    sourceSqueeze, realizeStep]

theorem source_relation_is_exact (input : V5TranscriptInputs) :
    sourceRelation input = relationSchedule.map (realizeStep input) := by
  simp [sourceRelation, relationSchedule, source_relation_round_is_exact]

theorem source_tail_is_exact (input : V5TranscriptInputs) :
    sourceTail input = tailSchedule.map (realizeStep input) := by
  simp [sourceTail, tailSchedule, sourceCheckAndAbsorb, workSchedule,
    sourceAbsorb, sourceSqueeze, realizeStep]

/-! ## Driver result and downstream consumption -/

def sourceAdapterDriver
    {FieldValue PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue) :
    V5TranscriptDriverResult FieldValue PointValue where
  trace := sourcePrefix input ++ sourceRelation input ++ sourceTail input
  consumed := {
    gamma := derived.gamma
    kappa := derived.kappa
    relationChallenges := derived.relationChallenge
    oodPoints := derived.oodPoint
    oodMixes := derived.oodMix
    foldChallenges := derived.foldChallenge
    selector := input.selector
    queryPositions := derived.queries
  }

theorem source_adapter_driver_is_exact
    {FieldValue PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue) :
    sourceAdapterDriver input derived =
      sourceShapedTranscriptDriver input derived := by
  unfold sourceAdapterDriver sourceShapedTranscriptDriver
  congr 1

/-- Expanding the adapter's typed calls yields the exact primitive hash-call
trace: one absorb hash, two hashes per squeezed block, and one non-advancing
grinding hash per work check. -/
theorem source_adapter_primitive_trace_is_exact
    {FieldValue PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue)
    (plan : SqueezeBlockPlan) :
    (sourceAdapterDriver input derived).trace.flatMap (expandEvent plan) =
      primitiveTranscriptTrace input plan := by
  rw [source_adapter_driver_is_exact]
  rfl

theorem source_adapter_hash_execution_is_exact
    {FieldValue PointValue : Type*}
    (hash : HashVector → Digest32)
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue)
    (plan : SqueezeBlockPlan) :
    executePrimitiveTrace hash
        ((sourceAdapterDriver input derived).trace.flatMap (expandEvent plan)) =
      executeCompleteTranscript hash input plan := by
  rw [source_adapter_primitive_trace_is_exact]
  rfl

theorem source_adapter_contains_exact_six_work_checks
    {FieldValue PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue) :
    ((sourceAdapterDriver input derived).trace.filterMap fun event =>
      match event with
      | .verifyWork kind _ _ => some kind
      | _ => none) = orderedWorkChecks ∧
      orderedWorkChecks.length = 6 := by
  rw [source_adapter_driver_is_exact]
  constructor
  · rfl
  · exact exact_schedule_cardinalities.2.2.2

/-- The universal equality is discharged for the explicit pure adapter, for
all repaired-body projections and all successful sampler outputs.  This does
not identify the production Rust functions with the adapter. -/
theorem exact_pure_adapter_driver_equality
    {FieldValue PointValue : Type*} :
    ExactRustV5TranscriptDriverEquality
      (fun pair : V5TranscriptInputs × V5DerivedValues FieldValue PointValue => pair.1)
      (fun pair : V5TranscriptInputs × V5DerivedValues FieldValue PointValue => pair.2)
      (fun pair => sourceAdapterDriver pair.1 pair.2) := by
  intro pair
  exact source_adapter_driver_is_exact pair.1 pair.2

theorem source_adapter_passes_exact_values_to_fri_and_relation
    {FieldValue PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue) :
    let consumed := (sourceAdapterDriver input derived).consumed
    consumed.gamma = derived.gamma ∧
      consumed.kappa = derived.kappa ∧
      consumed.relationChallenges = derived.relationChallenge ∧
      consumed.oodPoints = derived.oodPoint ∧
      consumed.oodMixes = derived.oodMix ∧
      consumed.foldChallenges = derived.foldChallenge ∧
      consumed.selector = input.selector ∧
      consumed.queryPositions = derived.queries := by
  simp [sourceAdapterDriver]

theorem source_adapter_queries_are_exact_without_replacement_output
    {FieldValue PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue)
    (blocks : List (FixedBytes 32))
    (hsuccess : derive18Queries blocks = some derived.queries) :
    let positions := (sourceAdapterDriver input derived).consumed.queryPositions
    positions.length = 18 ∧ positions.Nodup ∧
      (∀ query ∈ positions, query < 2 ^ 17) := by
  simpa [sourceAdapterDriver] using
    (derive18Queries_success_is_exact blocks derived.queries hsuccess)

#print axioms decoded_input_uses_exact_work_projection
#print axioms decoded_selector_is_exact_global_byte
#print axioms decoded_relation_and_fri_fields_are_exact_body_slices
#print axioms source_prefix_is_exact
#print axioms source_relation_is_exact
#print axioms source_tail_is_exact
#print axioms source_adapter_driver_is_exact
#print axioms source_adapter_primitive_trace_is_exact
#print axioms source_adapter_hash_execution_is_exact
#print axioms source_adapter_contains_exact_six_work_checks
#print axioms exact_pure_adapter_driver_equality
#print axioms source_adapter_passes_exact_values_to_fri_and_relation
#print axioms source_adapter_queries_are_exact_without_replacement_output

end AspisV5TranscriptSourceAdapter
