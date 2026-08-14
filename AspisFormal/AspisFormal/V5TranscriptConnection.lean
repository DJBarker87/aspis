import AspisFormal.V5NonceWorkAuthentication
import AspisFormal.V5M31RawMulReduction

/-!
# Exact V5 transcript schedule

This file models the accepted V5 verifier transcript at the level of calls to
`Transcript::absorb`, the challenge samplers, and the six grinding checks.  An
absorb event contains both the numeric Rust label and the complete byte
payload.  A squeeze event is named by the value it derives.  The primitive
expansion records how many `Transcript::squeeze_block` calls a successful
sampler execution used, so rejection paths are not collapsed into a
one-block assumption.

The three executable segments mirrored here are:

* `verify_v5_wire_prefix`;
* `replay_real_v5_relation_rounds`;
* `derive_v5_complete_queries_for_selector_from_transcript`.

The definitions and theorems below are unconditional Lean results about the
source-shaped model.  `ExactRustV5TranscriptDriverEquality`, near the end of
the file, is deliberately left as the precise Rust-to-Lean extraction
obligation.  Tests can exercise that equality on concrete inputs, but tests do
not discharge its universal quantifier.
-/

namespace AspisV5TranscriptConnection

open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5NonceWorkAuthentication

abbrev FixedBytes (n : Nat) := Fin n → Byte

def bytes {n : Nat} (value : FixedBytes n) : List Byte :=
  List.ofFn value

def zeroBytes (n : Nat) : List Byte :=
  List.replicate n 0

@[simp] theorem bytes_length {n : Nat} (value : FixedBytes n) :
    (bytes value).length = n := by
  exact List.length_ofFn

@[simp] theorem zeroBytes_length (n : Nat) :
    (zeroBytes n).length = n := by
  simp [zeroBytes]

/-! ## Exact inputs and framing bytes -/

/-- Every byte string read by the accepted transcript path.  Fixed-size
functions make the Rust widths part of the type instead of a side premise. -/
structure V5TranscriptInputs where
  statementDigest : FixedBytes 32
  /-- Layer zero is C1; layers one through three are the later FRI roots. -/
  circleRoot : Fin 4 → FixedBytes 32
  c2Root : FixedBytes 32
  /-- Salt zero belongs to C1, salt one to C2, and salts two through four to
  later layers one through three. -/
  publicSalt : Fin 5 → FixedBytes 32
  initialClaim : FixedBytes 16
  semanticSumcheck : Fin 10 → FixedBytes 448
  relationPoints : FixedBytes 480
  statementEvaluations : FixedBytes 1216
  terminalClaims : FixedBytes 48
  batchNonce : Nonce64
  inactiveClaim : FixedBytes 16
  oodValue : Fin 4 → Fin 2 → FixedBytes 16
  relationSumcheck : Fin 4 → FixedBytes 112
  foldNonce : Fin 4 → Nonce64
  finalPolynomial : FixedBytes 64
  finalNonce : Nonce64
  selector : Byte

/-- Exact bytes of `b"aspis-v5-real-witness-cu-v1"`. -/
def profileDomain : List Byte :=
  [97, 115, 112, 105, 115, 45, 118, 53, 45, 114, 101, 97, 108, 45,
    119, 105, 116, 110, 101, 115, 115, 45, 99, 117, 45, 118, 49]

/-- Exact bytes of `M31_CIRCLE_BASIS_DISCRIMINATOR`. -/
def circleBasisIdentifier : List Byte :=
  [97, 115, 112, 105, 115, 58, 99, 49, 58, 109, 51, 49, 45, 99, 105,
    114, 99, 108, 101, 58, 118, 48]

/-- The 28 bytes built by `begin_state_only_zerocheck`. -/
def stateOnlyConstraintRegistry : List Byte :=
  [1, 29, 95, 0, 10, 27, 28, 102, 0, 17, 48, 33, 175, 20,
    236, 180, 29, 18, 251, 234, 229, 239, 81, 34, 103, 18, 0, 0]

theorem exact_fixed_transcript_identifiers :
    profileDomain.length = 27 ∧
      circleBasisIdentifier.length = 22 ∧
      stateOnlyConstraintRegistry.length = 28 := by
  decide

/-! ## Absorb slots, labels, and payloads -/

inductive AbsorbSlot where
  | profile
  | basis
  | statement
  | circleRoot (layer : Fin 4)
  | c2Root
  | constraintRegistry
  | helperSum
  | maskClaim
  | semanticSumcheck (round : Fin 10)
  | relationPoints
  | statementEvaluations
  | terminalClaims
  | batchNonce
  | inactiveClaim
  | oodValue (round : Fin 4) (sample : Fin 2)
  | relationSumcheck (round : Fin 4)
  | foldNonce (round : Fin 4)
  | finalPolynomial
  | finalNonce
  | selector
  deriving DecidableEq, Fintype

/-- Numeric values from `aspis_core::transcript::label`. -/
def AbsorbSlot.label : AbsorbSlot → Byte
  | .profile => 1
  | .basis => 11
  | .statement => 2
  | .circleRoot _ => 12
  | .c2Root => 13
  | .constraintRegistry => 32
  | .helperSum => 33
  | .maskClaim => 31
  | .semanticSumcheck _ => 29
  | .relationPoints => 14
  | .statementEvaluations => 15
  | .terminalClaims => 6
  | .batchNonce => 28
  | .inactiveClaim => 10
  | .oodValue round _ => if round.val = 0 then 16 else 17
  | .relationSumcheck _ => 18
  | .foldNonce _ => 20
  | .finalPolynomial => 19
  | .finalNonce => 5
  | .selector => 44

def circleSaltIndex (layer : Fin 4) : Fin 5 :=
  if h : layer.val = 0 then 0 else ⟨layer.val + 1, by omega⟩

def roundByte (round : Fin 10) : Byte :=
  ⟨round.val, by omega⟩

def foldByte (round : Fin 4) : Byte :=
  ⟨round.val, by omega⟩

def sampleByte (sample : Fin 2) : Byte :=
  ⟨sample.val, by omega⟩

def roundRootPayload (input : V5TranscriptInputs) (layer : Fin 4) : List Byte :=
  foldByte layer ::
    (bytes (input.circleRoot layer) ++ bytes (input.publicSalt (circleSaltIndex layer)))

def c2RootPayload (input : V5TranscriptInputs) : List Byte :=
  bytes input.c2Root ++ bytes (input.publicSalt 1)

def maskClaimPayload (input : V5TranscriptInputs) : List Byte :=
  (27 : Byte) :: (10 : Byte) :: bytes input.initialClaim

def semanticSumcheckPayload
    (input : V5TranscriptInputs) (round : Fin 10) : List Byte :=
  roundByte round :: bytes (input.semanticSumcheck round)

def oodPayload
    (input : V5TranscriptInputs) (round : Fin 4) (sample : Fin 2) : List Byte :=
  foldByte round :: sampleByte sample :: bytes (input.oodValue round sample)

def relationSumcheckPayload
    (input : V5TranscriptInputs) (round : Fin 4) : List Byte :=
  foldByte round :: bytes (input.relationSumcheck round)

def V5TranscriptInputs.nonce (input : V5TranscriptInputs) : WorkKind → Nonce64
  | .batch => input.batchNonce
  | .fold round => input.foldNonce round
  | .finalQuery => input.finalNonce

def absorbPayload (input : V5TranscriptInputs) : AbsorbSlot → List Byte
  | .profile => profileDomain
  | .basis => circleBasisIdentifier
  | .statement => bytes input.statementDigest
  | .circleRoot layer => roundRootPayload input layer
  | .c2Root => c2RootPayload input
  | .constraintRegistry => stateOnlyConstraintRegistry
  | .helperSum => zeroBytes 16
  | .maskClaim => maskClaimPayload input
  | .semanticSumcheck round => semanticSumcheckPayload input round
  | .relationPoints => bytes input.relationPoints
  | .statementEvaluations => bytes input.statementEvaluations
  | .terminalClaims => bytes input.terminalClaims
  | .batchNonce => workAbsorbPayload .batch input.batchNonce
  | .inactiveClaim => bytes input.inactiveClaim
  | .oodValue round sample => oodPayload input round sample
  | .relationSumcheck round => relationSumcheckPayload input round
  | .foldNonce round => workAbsorbPayload (.fold round) (input.foldNonce round)
  | .finalPolynomial => bytes input.finalPolynomial
  | .finalNonce => workAbsorbPayload .finalQuery input.finalNonce
  | .selector => [input.selector]

def AbsorbSlot.payloadBytes : AbsorbSlot → Nat
  | .profile => 27
  | .basis => 22
  | .statement => 32
  | .circleRoot _ => 65
  | .c2Root => 64
  | .constraintRegistry => 28
  | .helperSum => 16
  | .maskClaim => 18
  | .semanticSumcheck _ => 449
  | .relationPoints => 480
  | .statementEvaluations => 1216
  | .terminalClaims => 48
  | .batchNonce => 8
  | .inactiveClaim => 16
  | .oodValue _ _ => 18
  | .relationSumcheck _ => 113
  | .foldNonce _ => 9
  | .finalPolynomial => 64
  | .finalNonce => 8
  | .selector => 1

theorem every_absorb_payload_has_exact_width
    (input : V5TranscriptInputs) (slot : AbsorbSlot) :
    (absorbPayload input slot).length = slot.payloadBytes := by
  cases slot <;>
    simp only [absorbPayload, AbsorbSlot.payloadBytes, roundRootPayload,
      c2RootPayload, maskClaimPayload, semanticSumcheckPayload, oodPayload,
      relationSumcheckPayload, bytes_length, zeroBytes_length,
      List.length_cons, List.length_append, List.length_nil,
      exact_work_absorb_payload_lengths] <;>
    norm_num [profileDomain, circleBasisIdentifier, stateOnlyConstraintRegistry]

theorem exact_root_and_public_salt_payloads (input : V5TranscriptInputs) :
    absorbPayload input (.circleRoot 0) =
        (0 : Byte) ::
          (bytes (input.circleRoot 0) ++ bytes (input.publicSalt 0)) ∧
      absorbPayload input .c2Root =
        bytes input.c2Root ++ bytes (input.publicSalt 1) ∧
      (∀ layer : Fin 4, layer.val ≠ 0 →
        absorbPayload input (.circleRoot layer) =
          foldByte layer ::
            (bytes (input.circleRoot layer) ++
              bytes (input.publicSalt ⟨layer.val + 1, by omega⟩))) := by
  constructor
  · rfl
  constructor
  · rfl
  intro layer hlayer
  simp [absorbPayload, roundRootPayload, circleSaltIndex, hlayer]

/-! ## Typed squeeze calls and the complete schedule -/

inductive SqueezeSlot where
  | lambda
  | chi
  | theta
  | zerocheckPoint (coordinate : Fin 10)
  | mu
  | eta
  | relationChallenge (round : Fin 10)
  | gamma
  | kappa
  | oodPoint (round : Fin 4) (sample : Fin 2)
  | oodMix (round : Fin 4) (sample : Fin 2)
  | foldChallenge (round : Fin 4)
  | queries
  deriving DecidableEq, Fintype

inductive ScheduleStep where
  | absorb (slot : AbsorbSlot)
  | squeeze (slot : SqueezeSlot)
  | verifyWork (kind : WorkKind)
  deriving DecidableEq

def workAbsorbSlot : WorkKind → AbsorbSlot
  | .batch => .batchNonce
  | .fold round => .foldNonce round
  | .finalQuery => .finalNonce

/-- A work helper is check first, absorb second. -/
def workSchedule (kind : WorkKind) : List ScheduleStep :=
  [.verifyWork kind, .absorb (workAbsorbSlot kind)]

def semanticRoundSchedule (round : Fin 10) : List ScheduleStep :=
  [.absorb (.semanticSumcheck round), .squeeze (.relationChallenge round)]

def oodSampleSchedule (round : Fin 4) (sample : Fin 2) : List ScheduleStep :=
  [.squeeze (.oodPoint round sample),
    .absorb (.oodValue round sample),
    .squeeze (.oodMix round sample)]

def laterLayer (round : Fin 4) : Option (Fin 4) :=
  if h : round.val + 1 < 4 then some ⟨round.val + 1, h⟩ else none

def relationRoundSchedule (round : Fin 4) : List ScheduleStep :=
  oodSampleSchedule round 0 ++
    oodSampleSchedule round 1 ++
    [.absorb (.relationSumcheck round)] ++
    workSchedule (.fold round) ++
    [.squeeze (.foldChallenge round)] ++
    (laterLayer round).toList.map (fun layer => .absorb (.circleRoot layer))

/-- Source-shaped trace of `verify_v5_wire_prefix`. -/
def prefixSchedule : List ScheduleStep :=
  [.absorb .profile,
    .absorb .basis,
    .absorb .statement,
    .absorb (.circleRoot 0),
    .squeeze .lambda,
    .squeeze .chi,
    .absorb .c2Root,
    .absorb .constraintRegistry,
    .absorb .helperSum,
    .squeeze .theta] ++
  (List.ofFn (fun coordinate : Fin 10 =>
    ScheduleStep.squeeze (.zerocheckPoint coordinate))) ++
  [.squeeze .mu,
    .absorb .maskClaim,
    .squeeze .eta] ++
  (List.ofFn semanticRoundSchedule).flatten ++
  [.absorb .relationPoints,
    .absorb .statementEvaluations,
    .absorb .terminalClaims] ++
  workSchedule .batch ++
  [.squeeze .gamma,
    .absorb .inactiveClaim,
    .squeeze .kappa]

/-- Source-shaped trace of `replay_real_v5_relation_rounds`. -/
def relationSchedule : List ScheduleStep :=
  (List.ofFn relationRoundSchedule).flatten

/-- Source-shaped trace of the final-polynomial/query helper. -/
def tailSchedule : List ScheduleStep :=
  [.absorb .finalPolynomial] ++
    workSchedule .finalQuery ++
    [.absorb .selector, .squeeze .queries]

def completeSchedule : List ScheduleStep :=
  prefixSchedule ++ relationSchedule ++ tailSchedule

inductive TranscriptEvent where
  | absorb (slot : AbsorbSlot) (label : Byte) (payload : List Byte)
  | squeeze (slot : SqueezeSlot)
  /-- The hash input is `(state, [3], nonce_le64)` and `difficulty` is the
  required number of leading zero bits. -/
  | verifyWork (kind : WorkKind) (difficulty : Nat) (nonceLE : List Byte)
  deriving DecidableEq

def realizeStep (input : V5TranscriptInputs) : ScheduleStep → TranscriptEvent
  | .absorb slot => .absorb slot slot.label (absorbPayload input slot)
  | .squeeze slot => .squeeze slot
  | .verifyWork kind =>
      .verifyWork kind kind.difficulty
        (List.ofFn (nonceLEBytes (input.nonce kind)))

def completeTranscriptTrace (input : V5TranscriptInputs) : List TranscriptEvent :=
  completeSchedule.map (realizeStep input)

theorem source_shaped_helper_composition_exact (input : V5TranscriptInputs) :
    completeTranscriptTrace input =
      prefixSchedule.map (realizeStep input) ++
        relationSchedule.map (realizeStep input) ++
        tailSchedule.map (realizeStep input) := by
  simp [completeTranscriptTrace, completeSchedule]

def ScheduleStep.absorbSlot? : ScheduleStep → Option AbsorbSlot
  | .absorb slot => some slot
  | _ => none

def ScheduleStep.squeezeSlot? : ScheduleStep → Option SqueezeSlot
  | .squeeze slot => some slot
  | _ => none

def ScheduleStep.workKind? : ScheduleStep → Option WorkKind
  | .verifyWork kind => some kind
  | _ => none

def orderedAbsorbSlots : List AbsorbSlot :=
  completeSchedule.filterMap ScheduleStep.absorbSlot?

def orderedSqueezeSlots : List SqueezeSlot :=
  completeSchedule.filterMap ScheduleStep.squeezeSlot?

def orderedWorkChecks : List WorkKind :=
  completeSchedule.filterMap ScheduleStep.workKind?

theorem exact_schedule_cardinalities :
    completeSchedule.length = 99 ∧
      orderedAbsorbSlots.length = 45 ∧
      orderedSqueezeSlots.length = 48 ∧
      orderedWorkChecks.length = 6 := by
  decide

theorem complete_schedule_has_no_duplicate_operation_slots :
    completeSchedule.Nodup := by
  decide

theorem every_absorb_slot_occurs_exactly_once :
    orderedAbsorbSlots.Nodup ∧
      ∀ slot : AbsorbSlot, slot ∈ orderedAbsorbSlots := by
  decide

theorem every_squeeze_slot_occurs_exactly_once :
    orderedSqueezeSlots.Nodup ∧
      ∀ slot : SqueezeSlot, slot ∈ orderedSqueezeSlots := by
  decide

theorem every_work_check_occurs_exactly_once :
    orderedWorkChecks.Nodup ∧
      ∀ kind : WorkKind, kind ∈ orderedWorkChecks := by
  decide

theorem work_is_checked_immediately_before_absorb
    (input : V5TranscriptInputs) (kind : WorkKind) :
    (workSchedule kind).map (realizeStep input) =
      [.verifyWork kind kind.difficulty
          (List.ofFn (nonceLEBytes (input.nonce kind))),
        .absorb (workAbsorbSlot kind) (workAbsorbSlot kind).label
          (absorbPayload input (workAbsorbSlot kind))] := by
  rfl

set_option maxRecDepth 10000 in
theorem complete_schedule_checks_each_work_immediately_before_absorb
    (kind : WorkKind) :
    (workSchedule kind).IsInfix completeSchedule := by
  fin_cases kind <;> decide

theorem swapping_distinct_absorb_slots_changes_order
    (left right : AbsorbSlot) (hne : left ≠ right) :
    [left, right] ≠ [right, left] := by
  simp [hne, Ne.symm hne]

theorem changing_an_absorb_payload_changes_the_event
    (slot : AbsorbSlot) (left right : List Byte) (hne : left ≠ right) :
    TranscriptEvent.absorb slot slot.label left ≠
      TranscriptEvent.absorb slot slot.label right := by
  simpa using hne

theorem omitting_any_scheduled_operation_changes_the_schedule
    (step : ScheduleStep) (hstep : step ∈ completeSchedule) :
    completeSchedule.erase step ≠ completeSchedule := by
  intro heq
  have hlength := congrArg List.length heq
  have hpositive : 0 < completeSchedule.length := by
    rw [exact_schedule_cardinalities.1]
    norm_num
  rw [List.length_erase_of_mem hstep] at hlength
  omega

theorem duplicating_any_scheduled_operation_changes_the_schedule
    (step : ScheduleStep) :
    completeSchedule ++ [step] ≠ completeSchedule := by
  intro heq
  have hlength := congrArg List.length heq
  simp at hlength

theorem swapping_distinct_scheduled_operations_changes_order
    (left right : ScheduleStep) (hne : left ≠ right) :
    [left, right] ≠ [right, left] := by
  simp [hne, Ne.symm hne]

/-! ## Primitive squeeze expansion -/

/-- A successful sampler witness records the exact number of calls to
`Transcript::squeeze_block` used at each typed squeeze slot.  One block is
the common path; larger values represent field rejection, zero/subfield/pole
rejection, or additional query blocks. -/
structure SqueezeBlockPlan where
  blocks : SqueezeSlot → Nat
  positive : ∀ slot, 0 < blocks slot
  queryBlocksAtMostEight : blocks .queries ≤ 8

inductive PrimitiveTranscriptEvent where
  | absorb (label : Byte) (payload : List Byte)
  /-- One call to `squeeze_block`, including its output hash and state-advance
  hash. -/
  | squeezeBlock
  | verifyWork (difficulty : Nat) (nonceLE : List Byte)
  deriving DecidableEq

/-! ### Exact `hashv` framing and state transition

The lists below retain `hashv` slice boundaries.  Thus `[state, [0, label],
payload]` is distinct in the model from one flattened byte string, and the
output and advance calls of `squeeze_block` remain two separate SHA-256
inputs.  The grinding difficulty controls acceptance but is intentionally not
hashed; this matches `Transcript::grinding_ok`.
-/

abbrev Digest32 := FixedBytes 32
abbrev HashVector := List (List Byte)

def initialTranscriptState : Digest32 := fun _ => 0

def absorbHashVector
    (state : Digest32) (label : Byte) (payload : List Byte) : HashVector :=
  [bytes state, [0, label], payload]

def squeezeOutputHashVector (state : Digest32) : HashVector :=
  [bytes state, [1]]

def squeezeAdvanceHashVector (state : Digest32) : HashVector :=
  [bytes state, [2]]

def grindingHashVector (state : Digest32) (nonceLE : List Byte) : HashVector :=
  [bytes state, [3], nonceLE]

theorem exact_transcript_hash_vector_framing
    (state : Digest32) (label : Byte) (payload nonceLE : List Byte) :
    absorbHashVector state label payload = [bytes state, [0, label], payload] ∧
      squeezeOutputHashVector state = [bytes state, [1]] ∧
      squeezeAdvanceHashVector state = [bytes state, [2]] ∧
      grindingHashVector state nonceLE = [bytes state, [3], nonceLE] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

structure HashTraceState where
  state : Digest32
  /-- Ordered SHA-256 `hashv` inputs, including their slice boundaries. -/
  vectors : List HashVector

def initialHashTraceState : HashTraceState where
  state := initialTranscriptState
  vectors := []

def executePrimitive
    (hash : HashVector → Digest32)
    (current : HashTraceState) : PrimitiveTranscriptEvent → HashTraceState
  | .absorb label payload =>
      let vector := absorbHashVector current.state label payload
      { state := hash vector
        vectors := current.vectors ++ [vector] }
  | .squeezeBlock =>
      let outputVector := squeezeOutputHashVector current.state
      let advanceVector := squeezeAdvanceHashVector current.state
      { state := hash advanceVector
        vectors := current.vectors ++ [outputVector, advanceVector] }
  | .verifyWork _ nonceLE =>
      let vector := grindingHashVector current.state nonceLE
      { state := current.state
        vectors := current.vectors ++ [vector] }

def executePrimitiveTrace
    (hash : HashVector → Digest32)
    (events : List PrimitiveTranscriptEvent) : HashTraceState :=
  events.foldl (executePrimitive hash) initialHashTraceState

theorem absorb_execution_uses_exact_label_and_payload
    (hash : HashVector → Digest32) (current : HashTraceState)
    (label : Byte) (payload : List Byte) :
    (executePrimitive hash current (.absorb label payload)).vectors =
      current.vectors ++ [[bytes current.state, [0, label], payload]] := by
  rfl

theorem squeeze_execution_uses_separate_output_and_advance_hashes
    (hash : HashVector → Digest32) (current : HashTraceState) :
    (executePrimitive hash current .squeezeBlock).vectors =
      current.vectors ++ [[bytes current.state, [1]], [bytes current.state, [2]]] ∧
    (executePrimitive hash current .squeezeBlock).state =
      hash [bytes current.state, [2]] := by
  exact ⟨rfl, rfl⟩

theorem work_execution_hashes_nonce_without_advancing_state
    (hash : HashVector → Digest32) (current : HashTraceState)
    (difficulty : Nat) (nonceLE : List Byte) :
    (executePrimitive hash current (.verifyWork difficulty nonceLE)).vectors =
        current.vectors ++ [[bytes current.state, [3], nonceLE]] ∧
      (executePrimitive hash current (.verifyWork difficulty nonceLE)).state =
        current.state := by
  exact ⟨rfl, rfl⟩

def expandEvent (plan : SqueezeBlockPlan) : TranscriptEvent → List PrimitiveTranscriptEvent
  | .absorb _ label payload => [.absorb label payload]
  | .squeeze slot => List.replicate (plan.blocks slot) .squeezeBlock
  | .verifyWork _ difficulty nonceLE => [.verifyWork difficulty nonceLE]

def primitiveTranscriptTrace
    (input : V5TranscriptInputs) (plan : SqueezeBlockPlan) :
    List PrimitiveTranscriptEvent :=
  (completeTranscriptTrace input).flatMap (expandEvent plan)

def executeCompleteTranscript
    (hash : HashVector → Digest32)
    (input : V5TranscriptInputs)
    (plan : SqueezeBlockPlan) : HashTraceState :=
  executePrimitiveTrace hash (primitiveTranscriptTrace input plan)

theorem every_typed_squeeze_expands_to_at_least_one_block
    (plan : SqueezeBlockPlan)
    (slot : SqueezeSlot) :
    (expandEvent plan (.squeeze slot)).length = plan.blocks slot ∧
      0 < (expandEvent plan (.squeeze slot)).length := by
  simp [expandEvent, plan.positive slot]

theorem query_squeeze_expands_to_at_most_eight_blocks
    (plan : SqueezeBlockPlan) :
    (expandEvent plan (.squeeze .queries)).length ≤ 8 := by
  simpa [expandEvent] using plan.queryBlocksAtMostEight

/-! ## Exact 18-query scan from squeeze blocks -/

def blockByte (block : FixedBytes 32) (word : Fin 8) (byte : Fin 4) : Byte :=
  block ⟨4 * word.val + byte.val, by omega⟩

def u32LE (block : FixedBytes 32) (word : Fin 8) : Nat :=
  (blockByte block word 0).val +
    2 ^ 8 * (blockByte block word 1).val +
    2 ^ 16 * (blockByte block word 2).val +
    2 ^ 24 * (blockByte block word 3).val

/-- `word & ((1 << 17) - 1)`, written as the equivalent remainder. -/
def queryCandidate (block : FixedBytes 32) (word : Fin 8) : Nat :=
  u32LE block word % 2 ^ 17

theorem rust_query_mask_equals_queryCandidate
    (block : FixedBytes 32) (word : Fin 8) :
    u32LE block word &&& (2 ^ 17 - 1) = queryCandidate block word := by
  exact AspisV5M31RawMulReduction.mask_low_eq_mod (u32LE block word) 17

def blockQueryCandidates (block : FixedBytes 32) : List Nat :=
  List.ofFn (queryCandidate block)

def firstUniqueAux (seen : List Nat) : List Nat → List Nat
  | [] => seen
  | value :: remaining =>
      firstUniqueAux
        (if value ∈ seen then seen else seen ++ [value]) remaining

def firstUnique (values : List Nat) : List Nat :=
  firstUniqueAux [] values

theorem firstUniqueAux_nodup
    (seen values : List Nat) (hseen : seen.Nodup) :
    (firstUniqueAux seen values).Nodup := by
  induction values generalizing seen with
  | nil => simpa [firstUniqueAux] using hseen
  | cons value remaining ih =>
      simp only [firstUniqueAux]
      split_ifs with hmem
      · exact ih seen hseen
      · apply ih (seen ++ [value])
        rw [List.nodup_append]
        refine ⟨hseen, by simp, ?_⟩
        intro member hmember singleton hsingleton
        simp only [List.mem_singleton] at hsingleton
        subst singleton
        intro heq
        apply hmem
        rw [← heq]
        exact hmember

theorem firstUnique_nodup (values : List Nat) :
    (firstUnique values).Nodup := by
  exact firstUniqueAux_nodup [] values (by simp)

theorem firstUniqueAux_preserves_predicate
    (predicate : Nat → Prop) (seen values : List Nat)
    (hseen : ∀ value ∈ seen, predicate value)
    (hvalues : ∀ value ∈ values, predicate value) :
    ∀ value ∈ firstUniqueAux seen values, predicate value := by
  induction values generalizing seen with
  | nil => simpa [firstUniqueAux] using hseen
  | cons head tail ih =>
      simp only [firstUniqueAux]
      have hhead : predicate head := hvalues head (by simp)
      have htail : ∀ value ∈ tail, predicate value := by
        intro value hvalue
        exact hvalues value (by simp [hvalue])
      split_ifs with hmem
      · exact ih seen hseen htail
      · apply ih (seen ++ [head])
        · intro value hvalue
          rcases List.mem_append.mp hvalue with hvalue | hvalue
          · exact hseen value hvalue
          · simp only [List.mem_singleton] at hvalue
            subst value
            exact hhead
        · exact htail

def boundedQueryCandidates (blocks : List (FixedBytes 32)) : List Nat :=
  (blocks.flatMap blockQueryCandidates).take 64

/-- Exact successful-output policy of
`challenge_queries_without_replacement(18, 1 << 17, 64)`.  The supplied
blocks are exactly those already squeezed by the transcript. -/
def derive18Queries (blocks : List (FixedBytes 32)) : Option (List Nat) :=
  let accepted := firstUnique (boundedQueryCandidates blocks)
  if 18 ≤ accepted.length then some (accepted.take 18) else none

theorem block_query_candidates_lt_bound
    (block : FixedBytes 32) :
    ∀ value ∈ blockQueryCandidates block, value < 2 ^ 17 := by
  intro value hvalue
  simp only [blockQueryCandidates, List.mem_ofFn] at hvalue
  rcases hvalue with ⟨word, rfl⟩
  exact Nat.mod_lt _ (by norm_num)

theorem bounded_query_candidates_lt_bound
    (blocks : List (FixedBytes 32)) :
    ∀ value ∈ boundedQueryCandidates blocks, value < 2 ^ 17 := by
  intro value hvalue
  have hflat : value ∈ blocks.flatMap blockQueryCandidates :=
    List.mem_of_mem_take hvalue
  rcases List.mem_flatMap.mp hflat with ⟨block, hblock, hvalue⟩
  exact block_query_candidates_lt_bound block value hvalue

theorem derive18Queries_success_is_exact
    (blocks : List (FixedBytes 32)) (queries : List Nat)
    (hsuccess : derive18Queries blocks = some queries) :
    queries.length = 18 ∧
      queries.Nodup ∧
      (∀ query ∈ queries, query < 2 ^ 17) := by
  rw [derive18Queries] at hsuccess
  split at hsuccess
  next henough =>
    simp only [Option.some.injEq] at hsuccess
    subst queries
    constructor
    · simp [List.length_take, min_eq_left henough]
    constructor
    · exact (firstUnique_nodup (boundedQueryCandidates blocks)).take
    · intro query hquery
      have hfirst : ∀ value ∈ firstUnique (boundedQueryCandidates blocks),
          value < 2 ^ 17 := by
        exact firstUniqueAux_preserves_predicate
          (fun value => value < 2 ^ 17) [] (boundedQueryCandidates blocks)
          (by simp) (bounded_query_candidates_lt_bound blocks)
      exact hfirst query (List.mem_of_mem_take hquery)
  next hshort => simp at hsuccess

/-! ## Values consumed by later verifier phases -/

inductive SqueezeResult (FieldValue PointValue : Type*) where
  | field (value : FieldValue)
  | point (value : PointValue)
  | queries (value : List Nat)

structure V5DerivedValues (FieldValue PointValue : Type*) where
  lambda : FieldValue
  chi : FieldValue
  theta : FieldValue
  zerocheckPoint : Fin 10 → FieldValue
  mu : FieldValue
  eta : FieldValue
  relationChallenge : Fin 10 → FieldValue
  gamma : FieldValue
  kappa : FieldValue
  oodPoint : Fin 4 → Fin 2 → PointValue
  oodMix : Fin 4 → Fin 2 → FieldValue
  foldChallenge : Fin 4 → FieldValue
  queries : List Nat

def SqueezeResult.fieldValue?
    {FieldValue PointValue : Type*} :
    SqueezeResult FieldValue PointValue → Option FieldValue
  | .field value => some value
  | _ => none

def SqueezeResult.pointValue?
    {FieldValue PointValue : Type*} :
    SqueezeResult FieldValue PointValue → Option PointValue
  | .point value => some value
  | _ => none

def SqueezeResult.queryValues?
    {FieldValue PointValue : Type*} :
    SqueezeResult FieldValue PointValue → Option (List Nat)
  | .queries value => some value
  | _ => none

def V5DerivedValues.at
    {FieldValue PointValue : Type*}
    (derived : V5DerivedValues FieldValue PointValue) :
    SqueezeSlot → SqueezeResult FieldValue PointValue
  | .lambda => .field derived.lambda
  | .chi => .field derived.chi
  | .theta => .field derived.theta
  | .zerocheckPoint coordinate => .field (derived.zerocheckPoint coordinate)
  | .mu => .field derived.mu
  | .eta => .field derived.eta
  | .relationChallenge round => .field (derived.relationChallenge round)
  | .gamma => .field derived.gamma
  | .kappa => .field derived.kappa
  | .oodPoint round sample => .point (derived.oodPoint round sample)
  | .oodMix round sample => .field (derived.oodMix round sample)
  | .foldChallenge round => .field (derived.foldChallenge round)
  | .queries => .queries derived.queries

/-- Values passed from transcript replay to the algebraic verifier. -/
structure V5VerifierConsumption (FieldValue PointValue : Type*) where
  gamma : FieldValue
  kappa : FieldValue
  relationChallenges : Fin 10 → FieldValue
  oodPoints : Fin 4 → Fin 2 → PointValue
  oodMixes : Fin 4 → Fin 2 → FieldValue
  foldChallenges : Fin 4 → FieldValue
  selector : Byte
  queryPositions : List Nat

def sourceShapedConsumption
    {FieldValue PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue) :
    V5VerifierConsumption FieldValue PointValue where
  gamma := derived.gamma
  kappa := derived.kappa
  relationChallenges := derived.relationChallenge
  oodPoints := derived.oodPoint
  oodMixes := derived.oodMix
  foldChallenges := derived.foldChallenge
  selector := input.selector
  queryPositions := derived.queries

theorem source_consumption_uses_exact_squeezes
    {FieldValue PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue) :
    let consumed := sourceShapedConsumption input derived
    consumed.gamma = derived.gamma ∧
      consumed.kappa = derived.kappa ∧
      consumed.relationChallenges = derived.relationChallenge ∧
      consumed.oodPoints = derived.oodPoint ∧
      consumed.oodMixes = derived.oodMix ∧
      consumed.foldChallenges = derived.foldChallenge ∧
      consumed.selector = input.selector ∧
      consumed.queryPositions = derived.queries := by
  simp [sourceShapedConsumption]

/-- Every downstream value is projected from the squeeze slot with the same
source name.  The selector is not squeezed: it is the one-byte absorbed value
immediately before the query sampler. -/
theorem source_consumption_uses_named_squeeze_results
    {FieldValue PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue) :
    let consumed := sourceShapedConsumption input derived
    (derived.at .gamma).fieldValue? = some consumed.gamma ∧
      (derived.at .kappa).fieldValue? = some consumed.kappa ∧
      (∀ round, (derived.at (.relationChallenge round)).fieldValue? =
        some (consumed.relationChallenges round)) ∧
      (∀ round sample, (derived.at (.oodPoint round sample)).pointValue? =
        some (consumed.oodPoints round sample)) ∧
      (∀ round sample, (derived.at (.oodMix round sample)).fieldValue? =
        some (consumed.oodMixes round sample)) ∧
      (∀ round, (derived.at (.foldChallenge round)).fieldValue? =
        some (consumed.foldChallenges round)) ∧
      absorbPayload input .selector = [consumed.selector] ∧
      (derived.at .queries).queryValues? = some consumed.queryPositions := by
  simp [sourceShapedConsumption, V5DerivedValues.at, SqueezeResult.fieldValue?,
    SqueezeResult.pointValue?, SqueezeResult.queryValues?, absorbPayload]

theorem source_query_positions_are_exact_18_query_decode
    {FieldValue PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue)
    (blocks : List (FixedBytes 32))
    (hdecode : derive18Queries blocks = some derived.queries) :
    let positions := (sourceShapedConsumption input derived).queryPositions
    positions = derived.queries ∧
      positions.length = 18 ∧
      positions.Nodup ∧
      (∀ query ∈ positions, query < 2 ^ 17) := by
  have hexact := derive18Queries_success_is_exact blocks derived.queries hdecode
  exact ⟨rfl, hexact⟩

structure V5TranscriptDriverResult (FieldValue PointValue : Type*) where
  trace : List TranscriptEvent
  consumed : V5VerifierConsumption FieldValue PointValue

def sourceShapedTranscriptDriver
    {FieldValue PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue) :
    V5TranscriptDriverResult FieldValue PointValue where
  trace := completeTranscriptTrace input
  consumed := sourceShapedConsumption input derived

/-- The smallest remaining executable equality after the source-shaped Lean
result: decode one accepted Rust body into `V5TranscriptInputs`, expose the
successful sampler outputs as `V5DerivedValues`, and show that the real driver
returns the same trace and consumed values as the model. -/
def ExactRustV5TranscriptDriverEquality
    {RustInput FieldValue PointValue : Type*}
    (decodeInput : RustInput → V5TranscriptInputs)
    (decodeDerived : RustInput → V5DerivedValues FieldValue PointValue)
    (rustDriver : RustInput → V5TranscriptDriverResult FieldValue PointValue) : Prop :=
  ∀ input,
    rustDriver input =
      sourceShapedTranscriptDriver (decodeInput input) (decodeDerived input)

theorem rust_driver_consumes_exact_squeezes_of_equality
    {RustInput FieldValue PointValue : Type*}
    (decodeInput : RustInput → V5TranscriptInputs)
    (decodeDerived : RustInput → V5DerivedValues FieldValue PointValue)
    (rustDriver : RustInput → V5TranscriptDriverResult FieldValue PointValue)
    (hequality : ExactRustV5TranscriptDriverEquality
      decodeInput decodeDerived rustDriver)
    (input : RustInput) :
    (rustDriver input).consumed =
      sourceShapedConsumption (decodeInput input) (decodeDerived input) := by
  rw [hequality input]
  rfl

#print axioms exact_fixed_transcript_identifiers
#print axioms every_absorb_payload_has_exact_width
#print axioms exact_root_and_public_salt_payloads
#print axioms source_shaped_helper_composition_exact
#print axioms exact_schedule_cardinalities
#print axioms complete_schedule_has_no_duplicate_operation_slots
#print axioms every_absorb_slot_occurs_exactly_once
#print axioms every_squeeze_slot_occurs_exactly_once
#print axioms every_work_check_occurs_exactly_once
#print axioms work_is_checked_immediately_before_absorb
#print axioms complete_schedule_checks_each_work_immediately_before_absorb
#print axioms omitting_any_scheduled_operation_changes_the_schedule
#print axioms exact_transcript_hash_vector_framing
#print axioms squeeze_execution_uses_separate_output_and_advance_hashes
#print axioms work_execution_hashes_nonce_without_advancing_state
#print axioms rust_query_mask_equals_queryCandidate
#print axioms derive18Queries_success_is_exact
#print axioms source_consumption_uses_exact_squeezes
#print axioms source_consumption_uses_named_squeeze_results
#print axioms source_query_positions_are_exact_18_query_decode
#print axioms rust_driver_consumes_exact_squeezes_of_equality

end AspisV5TranscriptConnection
