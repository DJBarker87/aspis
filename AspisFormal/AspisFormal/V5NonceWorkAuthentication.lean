import AspisFormal.V5ExactRuntimeWireRepair
import AspisFormal.SoundnessLedger
import AspisFormal.SoundnessWorkNormalizedEndpoint

/-!
# v5 positioned nonce-work authentication

This file records the six work predicates intended for the repaired mode-9
candidate grammar.  It separates three things that must not be conflated:

* byte placement and transcript position, proved here as finite arithmetic;
* an abstract executable predicate at each exact prefix, label, and difficulty;
* Rust/hash/random-oracle correspondence, retained as named interfaces.

The 37-bit batch predicate is checked after the terminal data and before
`gamma`; each fold predicate is checked before its own `alpha`; and the final
predicate is checked after the final polynomial and before selector/q18.
Numerically equal nonces are not forbidden: separation means six positioned
predicate instances, not six entropy samples.

The width-19 arithmetic below proves only that coefficient 18 is no worse than
the old coefficient 28 in the existing closed-form expression.  Applying that
expression to the actual direct-C event consumes both the explicit
`ExactV5Width19DirectCBatchApplicability` premise and a separately cited event
bound.  No schedule applicability or width-29 event reduction is silently
imported.
-/

namespace AspisV5NonceWorkAuthentication

open AspisFormal.V5ExactRuntimeWireRepair
open AspisSoundnessLedger
open AspisWorkNormalizedEndpoint

/-! ## Six exact work positions -/

inductive WorkKind where
  | batch
  | fold (round : Fin 4)
  | finalQuery
  deriving DecidableEq, Fintype

def foldDifficulty : Fin 4 → Nat
  | ⟨0, _⟩ => 34
  | ⟨1, _⟩ => 33
  | ⟨2, _⟩ => 30
  | ⟨3, _⟩ => 25

def WorkKind.difficulty : WorkKind → Nat
  | .batch => 37
  | .fold round => foldDifficulty round
  | .finalQuery => 32

/-- Transcript absorb labels from `aspis_core::transcript::label`: batch 28,
fold 20, and final grinding 5. -/
def WorkKind.label : WorkKind → Nat
  | .batch => 28
  | .fold _ => 20
  | .finalQuery => 5

inductive PrefixStage where
  | terminalBeforeGamma
  | foldBeforeAlpha (round : Fin 4)
  | finalPolynomialBeforeSelector
  deriving DecidableEq, Fintype

def WorkKind.stage : WorkKind → PrefixStage
  | .batch => .terminalBeforeGamma
  | .fold round => .foldBeforeAlpha round
  | .finalQuery => .finalPolynomialBeforeSelector

def WorkKind.offset : WorkKind → Nat
  | .batch => 11080
  | .fold round => 11048 + 8 * round.val
  | .finalQuery => 19127

def WorkKind.stop (kind : WorkKind) : Nat := kind.offset + 8

theorem exact_difficulty_map :
    WorkKind.difficulty .batch = 37 ∧
      WorkKind.difficulty (.fold 0) = 34 ∧
      WorkKind.difficulty (.fold 1) = 33 ∧
      WorkKind.difficulty (.fold 2) = 30 ∧
      WorkKind.difficulty (.fold 3) = 25 ∧
      WorkKind.difficulty .finalQuery = 32 := by
  decide

theorem exact_label_and_stage_map :
    WorkKind.label .batch = 28 ∧
      WorkKind.stage .batch = .terminalBeforeGamma ∧
      (∀ round, WorkKind.label (.fold round) = 20 ∧
        WorkKind.stage (.fold round) = .foldBeforeAlpha round) ∧
      WorkKind.label .finalQuery = 5 ∧
      WorkKind.stage .finalQuery = .finalPolynomialBeforeSelector := by
  simp [WorkKind.label, WorkKind.stage]

theorem work_kind_count_is_six : Fintype.card WorkKind = 6 := by
  decide

/-! ## Repaired mode-9 byte intervals -/

inductive WorkWireRegion where
  | foldNonces
  | batchNonce
  | remainingZero
  | finalNonce
  | selector
  deriving DecidableEq, Fintype

def WorkWireRegion.start : WorkWireRegion → Nat
  | .foldNonces => 11048
  | .batchNonce => 11080
  | .remainingZero => 11088
  | .finalNonce => 19127
  | .selector => 19135

def WorkWireRegion.stop : WorkWireRegion → Nat
  | .foldNonces => 11080
  | .batchNonce => 11088
  | .remainingZero => 11112
  | .finalNonce => 19135
  | .selector => 19136

def WorkWireRegion.Contains (region : WorkWireRegion) (offset : Nat) : Prop :=
  region.start ≤ offset ∧ offset < region.stop

def WorkWireRegion.Disjoint (left right : WorkWireRegion) : Prop :=
  left.stop ≤ right.start ∨ right.stop ≤ left.start

theorem exact_repaired_work_wire_offsets :
    WorkWireRegion.start .foldNonces = 11048 ∧
      WorkWireRegion.stop .foldNonces = 11080 ∧
      WorkWireRegion.start .batchNonce = 11080 ∧
      WorkWireRegion.stop .batchNonce = 11088 ∧
      WorkWireRegion.start .remainingZero = 11088 ∧
      WorkWireRegion.stop .remainingZero = 11112 ∧
      WorkWireRegion.start .finalNonce = finalNonceOffset ∧
      WorkWireRegion.stop .finalNonce = querySelectorOffset ∧
      WorkWireRegion.start .selector = querySelectorOffset ∧
      WorkWireRegion.stop .selector = repairedFixedBytes := by
  norm_num [WorkWireRegion.start, WorkWireRegion.stop, finalNonceOffset,
    querySelectorOffset, repairedFixedBytes]

theorem work_wire_regions_pairwise_disjoint :
    ∀ left right : WorkWireRegion, left ≠ right → left.Disjoint right := by
  intro left right hne
  fin_cases left <;> fin_cases right <;>
    simp_all [WorkWireRegion.Disjoint, WorkWireRegion.start,
      WorkWireRegion.stop]

theorem relation_final_block_exact_coverage (offset : Nat) :
    11048 ≤ offset ∧ offset < 11112 ↔
      WorkWireRegion.Contains .foldNonces offset ∨
      WorkWireRegion.Contains .batchNonce offset ∨
      WorkWireRegion.Contains .remainingZero offset := by
  simp only [WorkWireRegion.Contains, WorkWireRegion.start,
    WorkWireRegion.stop]
  omega

theorem final_nonce_selector_exact_coverage (offset : Nat) :
    19127 ≤ offset ∧ offset < repairedFixedBytes ↔
      WorkWireRegion.Contains .finalNonce offset ∨
      WorkWireRegion.Contains .selector offset := by
  norm_num [WorkWireRegion.Contains, WorkWireRegion.start,
    WorkWireRegion.stop, repairedFixedBytes]
  omega

theorem fold_nonce_slots_exact_and_disjoint (round : Fin 4) :
    WorkKind.offset (.fold round) = 11048 + 8 * round.val ∧
      WorkKind.stop (.fold round) ≤ 11080 := by
  simp [WorkKind.offset, WorkKind.stop]
  omega

theorem fold_nonce_slots_cover_exact_region (offset : Nat) :
    11048 ≤ offset ∧ offset < 11080 ↔
      ∃ round : Fin 4,
        WorkKind.offset (.fold round) ≤ offset ∧
          offset < WorkKind.stop (.fold round) := by
  constructor
  · rintro ⟨hstart, hstop⟩
    by_cases h0 : offset < 11056
    · exact ⟨0, by simp [WorkKind.offset, WorkKind.stop]; omega⟩
    · by_cases h1 : offset < 11064
      · exact ⟨1, by simp [WorkKind.offset, WorkKind.stop]; omega⟩
      · by_cases h2 : offset < 11072
        · exact ⟨2, by simp [WorkKind.offset, WorkKind.stop]; omega⟩
        · exact ⟨3, by simp [WorkKind.offset, WorkKind.stop]; omega⟩
  · rintro ⟨round, hround⟩
    have hslot := fold_nonce_slots_exact_and_disjoint round
    constructor <;> omega

theorem distinct_fold_rounds_have_distinct_wire_slots
    {left right : Fin 4} (hne : left ≠ right) :
    WorkKind.offset (.fold left) ≠ WorkKind.offset (.fold right) := by
  intro heq
  simp only [WorkKind.offset] at heq
  have hval : left.val = right.val := by omega
  exact hne (Fin.ext hval)

/-- Concrete regression tooth: exchanging fold zero and fold one is not a
position-preserving serialization. -/
theorem swapping_fold_zero_and_one_changes_position :
    WorkKind.offset (.fold 0) = 11048 ∧
      WorkKind.offset (.fold 1) = 11056 ∧
      WorkKind.offset (.fold 0) ≠ WorkKind.offset (.fold 1) := by
  norm_num [WorkKind.offset]

/-- Concrete regression tooth: batch and final work have different fields,
stages, labels, and difficulties.  One positioned predicate cannot be booked
as the other merely because both payloads are eight-byte nonces. -/
theorem batch_and_final_are_not_substitutable :
    WorkKind.offset .batch ≠ WorkKind.offset .finalQuery ∧
      WorkKind.stage .batch ≠ WorkKind.stage .finalQuery ∧
      WorkKind.label .batch ≠ WorkKind.label .finalQuery ∧
      WorkKind.difficulty .batch ≠ WorkKind.difficulty .finalQuery := by
  decide

/-! ### Every nonce byte has one exact global position -/

structure PositionedNonceByte where
  kind : WorkKind
  localByte : Fin 8
  deriving DecidableEq, Fintype

def positionedNonceByteOffset (coordinate : PositionedNonceByte) : Nat :=
  coordinate.kind.offset + coordinate.localByte.val

theorem positioned_nonce_byte_offset_lt_fixed_body
    (coordinate : PositionedNonceByte) :
    positionedNonceByteOffset coordinate < repairedFixedBytes := by
  rcases coordinate with ⟨kind, localByte⟩
  have hlocal := localByte.isLt
  cases kind with
  | batch =>
      norm_num [positionedNonceByteOffset, WorkKind.offset, repairedFixedBytes]
      omega
  | fold round =>
      have hround := round.isLt
      norm_num [positionedNonceByteOffset, WorkKind.offset, repairedFixedBytes]
      omega
  | finalQuery =>
      norm_num [positionedNonceByteOffset, WorkKind.offset, repairedFixedBytes]
      omega

def positionedNonceByteFin
    (coordinate : PositionedNonceByte) : Fin repairedFixedBytes :=
  ⟨positionedNonceByteOffset coordinate,
    positioned_nonce_byte_offset_lt_fixed_body coordinate⟩

theorem work_kind_nonce_slots_pairwise_disjoint :
    ∀ left right : WorkKind, left ≠ right →
      left.stop ≤ right.offset ∨ right.stop ≤ left.offset := by
  intro left right hne
  cases left with
  | batch =>
      cases right with
      | batch => contradiction
      | fold round =>
          right
          simp [WorkKind.stop, WorkKind.offset]
          omega
      | finalQuery =>
          left
          norm_num [WorkKind.stop, WorkKind.offset]
  | fold leftRound =>
      cases right with
      | batch =>
          left
          simp [WorkKind.stop, WorkKind.offset]
          omega
      | fold rightRound =>
          have hround : leftRound ≠ rightRound := by
            intro heq
            subst rightRound
            exact hne rfl
          have hval : leftRound.val ≠ rightRound.val := by
            intro heq
            exact hround (Fin.ext heq)
          simp only [WorkKind.stop, WorkKind.offset]
          omega
      | finalQuery =>
          left
          simp [WorkKind.stop, WorkKind.offset]
          omega
  | finalQuery =>
      cases right with
      | batch =>
          right
          norm_num [WorkKind.stop, WorkKind.offset]
      | fold round =>
          right
          simp [WorkKind.stop, WorkKind.offset]
          omega
      | finalQuery => contradiction

theorem positioned_nonce_byte_offset_injective :
    Function.Injective positionedNonceByteOffset := by
  intro left right heq
  by_cases hkind : left.kind = right.kind
  · cases left with
    | mk leftKind leftByte =>
        cases right with
        | mk rightKind rightByte =>
            simp only at hkind
            subst rightKind
            simp only [positionedNonceByteOffset] at heq
            have hbyte : leftByte = rightByte := Fin.ext (by omega)
            subst rightByte
            rfl
  · have hdisjoint := work_kind_nonce_slots_pairwise_disjoint
      left.kind right.kind hkind
    have hleft := left.localByte.isLt
    have hright := right.localByte.isLt
    simp only [WorkKind.stop] at hdisjoint
    simp only [positionedNonceByteOffset] at heq
    omega

def IsExactNonceWireOffset (offset : Nat) : Prop :=
  ∃ kind : WorkKind, kind.offset ≤ offset ∧ offset < kind.stop

abbrev ExactNonceWireByte :=
  { offset : Fin repairedFixedBytes // IsExactNonceWireOffset offset.val }

def positionedNonceByteToExactWire
    (coordinate : PositionedNonceByte) : ExactNonceWireByte :=
  ⟨positionedNonceByteFin coordinate, coordinate.kind, by
    simp only [positionedNonceByteFin, positionedNonceByteOffset,
      WorkKind.stop]
    have hlocal := coordinate.localByte.isLt
    omega⟩

theorem positioned_nonce_bytes_biject_exact_48_wire_bytes :
    Function.Bijective positionedNonceByteToExactWire := by
  constructor
  · intro left right heq
    apply positioned_nonce_byte_offset_injective
    have hfin := congrArg (fun value : ExactNonceWireByte => value.1.val) heq
    exact hfin
  · intro target
    rcases target.property with ⟨kind, hstart, hstop⟩
    let localByte : Fin 8 := ⟨target.val.val - kind.offset, by
      simp only [WorkKind.stop] at hstop
      omega⟩
    let coordinate : PositionedNonceByte := ⟨kind, localByte⟩
    refine ⟨coordinate, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    simp only [positionedNonceByteToExactWire, positionedNonceByteFin,
      positionedNonceByteOffset, coordinate, localByte]
    change kind.offset + (target.val.val - kind.offset) = target.val.val
    omega

theorem positioned_nonce_byte_count_is_48 :
    Fintype.card PositionedNonceByte = 48 := by
  decide

def positionedNonceRuntimeOffset (shape : RuntimeShape)
    (coordinate : PositionedNonceByte) : Fin (runtimeRepairedProofBytes shape) :=
  ⟨positionedNonceByteOffset coordinate, by
    have hfixed := positioned_nonce_byte_offset_lt_fixed_body coordinate
    simp only [runtimeRepairedProofBytes]
    omega⟩

theorem positioned_nonce_runtime_offset_injective (shape : RuntimeShape) :
    Function.Injective (positionedNonceRuntimeOffset shape) := by
  intro left right heq
  apply positioned_nonce_byte_offset_injective
  exact congrArg Fin.val heq

/-! ### Exact structured work projection on an already accepted body

The imported runtime grammar proves exact total length, but its `parseExact`
does not perform Rust's semantic validation.  Consequently no theorem here
equates the strict Rust parser with `parseExact`.  We instead project the exact
work bytes from a body that an external executable parser has already accepted.
-/

/-- A deployed nonce is a bounded unsigned 64-bit integer. -/
abbrev Nonce64 := Fin (2 ^ 64)

abbrev LE64Bytes := Fin 8 → Byte

/-- The explicit little-endian byte formula used by Rust's `u64::to_le_bytes`.
The `i`th byte is `(nonce / 2^(8i)) mod 256`. -/
def nonceLEByte (nonce : Nonce64) (localByte : Fin 8) : Byte :=
  ⟨(nonce.val / 2 ^ (8 * localByte.val)) % 256, Nat.mod_lt _ (by norm_num)⟩

def nonceLEBytes (nonce : Nonce64) : LE64Bytes :=
  fun localByte => nonceLEByte nonce localByte

/-- An exact eight-byte representation paired with the bounded value it
encodes.  This avoids pretending that an arbitrary eight-byte string was
semantically parsed. -/
structure ExactLE64Payload where
  nonce : Nonce64
  bytes : LE64Bytes
  canonical : bytes = nonceLEBytes nonce

def encodeExactLE64 (nonce : Nonce64) : ExactLE64Payload where
  nonce := nonce
  bytes := nonceLEBytes nonce
  canonical := rfl

def decodeExactLE64 (payload : ExactLE64Payload) : Nonce64 := payload.nonce

theorem decode_encode_exact_le64 (nonce : Nonce64) :
    decodeExactLE64 (encodeExactLE64 nonce) = nonce := by
  rfl

theorem encode_decode_exact_le64 (payload : ExactLE64Payload) :
    encodeExactLE64 (decodeExactLE64 payload) = payload := by
  rcases payload with ⟨nonce, bytes, canonical⟩
  subst bytes
  rfl

/-- Exact `AV5CUP08` account-body magic. -/
def av5CUP08 : Fin 8 → Byte :=
  ![65, 86, 53, 67, 85, 80, 48, 56]

theorem av5CUP08_is_exact_ascii :
    List.ofFn av5CUP08 = [65, 86, 53, 67, 85, 80, 48, 56] := by
  decide

/-- Read one byte from an exact runtime body.  Exact length is used only to
justify the bounded read, never as semantic parser acceptance. -/
def runtimeWireByteAt (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (offset : Fin (runtimeRepairedProofBytes shape)) : Byte :=
  wire.1.get ⟨offset.val, by
    rw [wire.property]
    exact offset.isLt⟩

def magicRuntimeOffset (shape : RuntimeShape) (localByte : Fin 8) :
    Fin (runtimeRepairedProofBytes shape) :=
  ⟨localByte.val, by
    have hlocal := localByte.isLt
    simp only [runtimeRepairedProofBytes, repairedFixedBytes]
    omega⟩

abbrev RemainingZeroByte := Fin 24

def remainingZeroRuntimeOffset (shape : RuntimeShape)
    (localByte : RemainingZeroByte) : Fin (runtimeRepairedProofBytes shape) :=
  ⟨11088 + localByte.val, by
    have hlocal := localByte.isLt
    simp only [runtimeRepairedProofBytes, repairedFixedBytes]
    omega⟩

structure WorkWireView where
  nonces : WorkKind → Nonce64

/-- Raw projection of precisely the work-relevant bytes from an already
length-bounded body. -/
structure ProjectedWorkWire where
  accountMagic : Fin 8 → Byte
  noncePayload : WorkKind → LE64Bytes
  remainingZero : RemainingZeroByte → Byte

def projectWorkWire (shape : RuntimeShape) (wire : RuntimeExactWire shape) :
    ProjectedWorkWire where
  accountMagic := fun localByte =>
    runtimeWireByteAt shape wire (magicRuntimeOffset shape localByte)
  noncePayload := fun kind localByte =>
    runtimeWireByteAt shape wire
      (positionedNonceRuntimeOffset shape ⟨kind, localByte⟩)
  remainingZero := fun localByte =>
    runtimeWireByteAt shape wire (remainingZeroRuntimeOffset shape localByte)

def canonicalWorkWire (view : WorkWireView) : ProjectedWorkWire where
  accountMagic := av5CUP08
  noncePayload := fun kind => nonceLEBytes (view.nonces kind)
  remainingZero := fun _ => 0

/-- Exact work-field projection for the current accepted grammar: magic,
four fold nonces, batch nonce, the canonical 24-byte zero tail, and final
nonce all agree byte-for-byte at their global offsets. -/
def ExactWorkWireProjection (shape : RuntimeShape)
    (wire : RuntimeExactWire shape) (view : WorkWireView) : Prop :=
  projectWorkWire shape wire = canonicalWorkWire view

/-- Precise Rust seam.  `rustAcceptsBody` is the actual strict parser/verifier
acceptance predicate and `rustProjectNonces` is its actual six-field
projection.  This claims equality only on this already accepted body; it does
not identify the whole Rust parser with the length-only model parser. -/
def ExactRustAcceptedWorkWireProjection (shape : RuntimeShape)
    (rustAcceptsBody : List Byte → Prop)
    (rustProjectNonces : List Byte → Option (WorkKind → Nonce64))
    (wire : RuntimeExactWire shape) (view : WorkWireView) : Prop :=
  rustAcceptsBody (serializeRuntimeExact shape wire) ∧
    rustProjectNonces (serializeRuntimeExact shape wire) = some view.nonces ∧
    ExactWorkWireProjection shape wire view

theorem model_project_recovers_work_wire_byte_for_byte
    (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (view : WorkWireView)
    (hprojection : ExactWorkWireProjection shape wire view) :
    projectWorkWire shape wire = canonicalWorkWire view :=
  hprojection

/-- Model parse/project theorem: under the exact accepted-body projection,
all six projected payloads form canonical LE64 values and decode to precisely
the six bounded nonces, byte-for-byte. -/
theorem model_parse_project_recovers_all_six_nonces_byte_for_byte
    (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (view : WorkWireView)
    (hprojection : ExactWorkWireProjection shape wire view) :
    ∀ kind, ∃ payload : ExactLE64Payload,
      payload.bytes = (projectWorkWire shape wire).noncePayload kind ∧
        decodeExactLE64 payload = view.nonces kind := by
  intro kind
  refine ⟨encodeExactLE64 (view.nonces kind), ?_, rfl⟩
  have hbytes := congrArg (fun projection => projection.noncePayload kind) hprojection
  exact hbytes.symm

theorem rust_accepted_projection_recovers_all_six_nonces
    (shape : RuntimeShape)
    (rustAcceptsBody : List Byte → Prop)
    (rustProjectNonces : List Byte → Option (WorkKind → Nonce64))
    (wire : RuntimeExactWire shape) (view : WorkWireView)
    (hcorrespondence : ExactRustAcceptedWorkWireProjection shape
      rustAcceptsBody rustProjectNonces wire view) :
    rustAcceptsBody (serializeRuntimeExact shape wire) ∧
      rustProjectNonces (serializeRuntimeExact shape wire) = some view.nonces ∧
      (∀ kind, (projectWorkWire shape wire).noncePayload kind =
        nonceLEBytes (view.nonces kind)) := by
  refine ⟨hcorrespondence.1, hcorrespondence.2.1, ?_⟩
  intro kind
  exact congrArg (fun projection => projection.noncePayload kind)
    hcorrespondence.2.2

/-- Exact absorbed payload: folds use `[round || nonce_le64]`; batch and
final work use only `nonce_le64`. -/
def workAbsorbPayload (kind : WorkKind) (nonce : Nonce64) : List Byte :=
  match kind with
  | .fold round =>
      (⟨round.val, by have := round.isLt; omega⟩ : Byte) ::
        List.ofFn (nonceLEBytes nonce)
  | .batch | .finalQuery => List.ofFn (nonceLEBytes nonce)

theorem exact_work_absorb_payload_lengths (kind : WorkKind) (nonce : Nonce64) :
    (workAbsorbPayload kind nonce).length =
      match kind with
      | .fold _ => 9
      | .batch | .finalQuery => 8 := by
  cases kind <;> simp [workAbsorbPayload]

theorem fold_absorb_payload_is_round_then_le64
    (round : Fin 4) (nonce : Nonce64) :
    workAbsorbPayload (.fold round) nonce =
      (⟨round.val, by have := round.isLt; omega⟩ : Byte) ::
        List.ofFn (nonceLEBytes nonce) := by
  rfl

theorem batch_and_final_absorb_payloads_are_le64 (nonce : Nonce64) :
    workAbsorbPayload .batch nonce = List.ofFn (nonceLEBytes nonce) ∧
      workAbsorbPayload .finalQuery nonce = List.ofFn (nonceLEBytes nonce) := by
  exact ⟨rfl, rfl⟩

/-! ## Exact executable work step and acceptance -/

/-- The immediate operation after a successful work absorb.  The final case
explicitly includes selector absorption before the q18 draw. -/
inductive NextWorkAction where
  | sampleGamma
  | sampleFoldAlpha (round : Fin 4)
  | absorbSelectorThenSampleQ18
  deriving DecidableEq, Fintype

def WorkKind.nextAction : WorkKind → NextWorkAction
  | .batch => .sampleGamma
  | .fold round => .sampleFoldAlpha round
  | .finalQuery => .absorbSelectorThenSampleQ18

structure PositionedWorkInputs (State Challenge : Type*) where
  stateBefore : WorkKind → State
  nonce : WorkKind → Nonce64
  stateAfter : WorkKind → State
  nextResult : WorkKind → Challenge

/-- These are the executable operations, with the same argument split as the
Rust transcript: grinding checks `(state,bits,nonce)`, absorption receives the
fixed label and exact payload, and the next operation consumes the post-absorb
state. -/
structure ExecutableWorkFunctions (State Challenge : Type*) where
  grindingOK : State → Nat → Nonce64 → Prop
  absorb : State → Nat → List Byte → State
  executeNext : State → NextWorkAction → Challenge

/-- One exact deployed work step.  Unlike the former arbitrary five-argument
`check`, this proposition also fixes the absorb label/payload and the ordering
of the following challenge-producing operation. -/
def ExactWorkOK {State Challenge : Type*}
    (functions : ExecutableWorkFunctions State Challenge)
    (inputs : PositionedWorkInputs State Challenge) (kind : WorkKind) : Prop :=
  functions.grindingOK (inputs.stateBefore kind) kind.difficulty
      (inputs.nonce kind) ∧
    inputs.stateAfter kind =
      functions.absorb (inputs.stateBefore kind) kind.label
        (workAbsorbPayload kind (inputs.nonce kind)) ∧
    inputs.nextResult kind =
      functions.executeNext (inputs.stateAfter kind) kind.nextAction

structure ExecutableWorkAcceptance {State Challenge : Type*}
    (functions : ExecutableWorkFunctions State Challenge)
    (inputs : PositionedWorkInputs State Challenge) : Prop where
  everyWorkOK : ∀ kind, ExactWorkOK functions inputs kind

theorem acceptance_projects_every_exact_work_ok
    {State Challenge : Type*}
    {functions : ExecutableWorkFunctions State Challenge}
    {inputs : PositionedWorkInputs State Challenge}
    (accepted : ExecutableWorkAcceptance functions inputs) (kind : WorkKind) :
    ExactWorkOK functions inputs kind :=
  accepted.everyWorkOK kind

theorem acceptance_projects_batch_before_gamma
    {State Challenge : Type*}
    {functions : ExecutableWorkFunctions State Challenge}
    {inputs : PositionedWorkInputs State Challenge}
    (accepted : ExecutableWorkAcceptance functions inputs) :
    functions.grindingOK (inputs.stateBefore .batch) 37
        (inputs.nonce .batch) ∧
      inputs.stateAfter .batch =
        functions.absorb (inputs.stateBefore .batch) 28
          (List.ofFn (nonceLEBytes (inputs.nonce .batch))) ∧
      inputs.nextResult .batch =
        functions.executeNext (inputs.stateAfter .batch) .sampleGamma := by
  exact accepted.everyWorkOK .batch

theorem acceptance_projects_each_fold_before_its_alpha
    {State Challenge : Type*}
    {functions : ExecutableWorkFunctions State Challenge}
    {inputs : PositionedWorkInputs State Challenge}
    (accepted : ExecutableWorkAcceptance functions inputs) (round : Fin 4) :
    functions.grindingOK (inputs.stateBefore (.fold round))
        (foldDifficulty round) (inputs.nonce (.fold round)) ∧
      inputs.stateAfter (.fold round) =
        functions.absorb (inputs.stateBefore (.fold round)) 20
          ((⟨round.val, by have := round.isLt; omega⟩ : Byte) ::
            List.ofFn (nonceLEBytes (inputs.nonce (.fold round)))) ∧
      inputs.nextResult (.fold round) =
        functions.executeNext (inputs.stateAfter (.fold round))
          (.sampleFoldAlpha round) := by
  exact accepted.everyWorkOK (.fold round)

theorem acceptance_projects_final_before_selector
    {State Challenge : Type*}
    {functions : ExecutableWorkFunctions State Challenge}
    {inputs : PositionedWorkInputs State Challenge}
    (accepted : ExecutableWorkAcceptance functions inputs) :
    functions.grindingOK (inputs.stateBefore .finalQuery) 32
        (inputs.nonce .finalQuery) ∧
      inputs.stateAfter .finalQuery =
        functions.absorb (inputs.stateBefore .finalQuery) 5
          (List.ofFn (nonceLEBytes (inputs.nonce .finalQuery))) ∧
      inputs.nextResult .finalQuery =
        functions.executeNext (inputs.stateAfter .finalQuery)
          .absorbSelectorThenSampleQ18 := by
  exact accepted.everyWorkOK .finalQuery

def HonestMinerReturningValid {State Challenge : Type*}
    (functions : ExecutableWorkFunctions State Challenge)
    (inputs : PositionedWorkInputs State Challenge) : Prop :=
  ∀ kind, functions.grindingOK (inputs.stateBefore kind) kind.difficulty
    (inputs.nonce kind)

def ExactTranscriptWorkProgression {State Challenge : Type*}
    (functions : ExecutableWorkFunctions State Challenge)
    (inputs : PositionedWorkInputs State Challenge) : Prop :=
  ∀ kind,
    inputs.stateAfter kind =
        functions.absorb (inputs.stateBefore kind) kind.label
          (workAbsorbPayload kind (inputs.nonce kind)) ∧
      inputs.nextResult kind =
        functions.executeNext (inputs.stateAfter kind) kind.nextAction

/-- Honest mining alone is deliberately insufficient: acceptance also consumes
the exact post-check absorb and next-action progression. -/
theorem honest_miner_and_exact_progression_imply_accepted
    {State Challenge : Type*}
    {functions : ExecutableWorkFunctions State Challenge}
    {inputs : PositionedWorkInputs State Challenge}
    (hminer : HonestMinerReturningValid functions inputs)
    (hprogression : ExactTranscriptWorkProgression functions inputs) :
    ExecutableWorkAcceptance functions inputs := by
  constructor
  intro kind
  exact ⟨hminer kind, hprogression kind⟩

/-! ## Named deployment seams -/

/-- Exact input to `Transcript::grinding_ok`: the fixed domain byte `0x03`
followed by the eight little-endian nonce bytes.  The transcript state is a
separate hash-vector component. -/
def grindingHashPayload (nonce : Nonce64) : List Byte :=
  (3 : Byte) :: List.ofFn (nonceLEBytes nonce)

/-- Computational SHA/random-oracle interface only.  It maps the actual fixed
three-argument grinding operation to `hash(state, 0x03 || nonce_le64)`; it does
not assert that SHA is a random oracle. -/
def HashRandomOracleWorkInterface {State Digest : Type*}
    (hash : State → List Byte → Digest)
    (digestHasLeadingZeroBits : Digest → Nat → Prop)
    (grindingOK : State → Nat → Nonce64 → Prop) : Prop :=
  ∀ state bits nonce,
    grindingOK state bits nonce ↔
      digestHasLeadingZeroBits (hash state (grindingHashPayload nonce)) bits

/-- Exact executable correspondence.  The functions supplied here are the
actual Rust grind, absorb, and successor operations; acceptance is equated to
all six full steps, not merely to an arbitrary predicate that may ignore its
arguments. -/
structure ExactRustWorkVerifierCorrespondence
    {State Challenge Digest : Type*}
    (rustAccepts : Prop)
    (rustHash : State → List Byte → Digest)
    (digestHasLeadingZeroBits : Digest → Nat → Prop)
    (rustFunctions : ExecutableWorkFunctions State Challenge)
    (inputs : PositionedWorkInputs State Challenge) : Prop where
  exactGrindingHashInput : HashRandomOracleWorkInterface rustHash
    digestHasLeadingZeroBits rustFunctions.grindingOK
  acceptanceIffExactSixSteps : rustAccepts ↔
    ExecutableWorkAcceptance rustFunctions inputs

/-- Explicit transcript-position binding seam.  A changed nonce either fails
the exact fixed grinding predicate or changes the post-absorb state produced
with the exact label and payload. -/
def HashWorkTranscriptBinding {State Challenge : Type*}
    (functions : ExecutableWorkFunctions State Challenge)
    (inputs : PositionedWorkInputs State Challenge) : Prop :=
  ∀ kind replacement, replacement ≠ inputs.nonce kind →
    (¬ functions.grindingOK (inputs.stateBefore kind) kind.difficulty replacement) ∨
      functions.absorb (inputs.stateBefore kind) kind.label
          (workAbsorbPayload kind replacement) ≠
        functions.absorb (inputs.stateBefore kind) kind.label
          (workAbsorbPayload kind (inputs.nonce kind))

theorem changing_positioned_nonce_rejects_or_changes_post_state
    {State Challenge : Type*}
    {functions : ExecutableWorkFunctions State Challenge}
    {inputs : PositionedWorkInputs State Challenge}
    (hbinding : HashWorkTranscriptBinding functions inputs)
    (kind : WorkKind) (replacement : Nonce64)
    (hchanged : replacement ≠ inputs.nonce kind) :
    (¬ functions.grindingOK (inputs.stateBefore kind) kind.difficulty replacement) ∨
      functions.absorb (inputs.stateBefore kind) kind.label
          (workAbsorbPayload kind replacement) ≠
        functions.absorb (inputs.stateBefore kind) kind.label
          (workAbsorbPayload kind (inputs.nonce kind)) :=
  hbinding kind replacement hchanged

theorem insufficient_work_at_any_position_rejects
    {State Challenge : Type*}
    {functions : ExecutableWorkFunctions State Challenge}
    {inputs : PositionedWorkInputs State Challenge}
    (kind : WorkKind)
    (hbad : ¬ functions.grindingOK (inputs.stateBefore kind) kind.difficulty
      (inputs.nonce kind)) :
    ¬ ExecutableWorkAcceptance functions inputs := by
  intro accepted
  exact hbad (accepted.everyWorkOK kind).1

theorem swapping_distinct_fold_nonces_rejects_or_changes_positioned_states
    {State Challenge : Type*}
    {functions : ExecutableWorkFunctions State Challenge}
    {inputs : PositionedWorkInputs State Challenge}
    (hbinding : HashWorkTranscriptBinding functions inputs)
    (left right : Fin 4)
    (hvalues : inputs.nonce (.fold left) ≠ inputs.nonce (.fold right)) :
    ((¬ functions.grindingOK (inputs.stateBefore (.fold left))
          (foldDifficulty left) (inputs.nonce (.fold right))) ∨
        functions.absorb (inputs.stateBefore (.fold left)) 20
            (workAbsorbPayload (.fold left) (inputs.nonce (.fold right))) ≠
          functions.absorb (inputs.stateBefore (.fold left)) 20
            (workAbsorbPayload (.fold left) (inputs.nonce (.fold left)))) ∧
      ((¬ functions.grindingOK (inputs.stateBefore (.fold right))
          (foldDifficulty right) (inputs.nonce (.fold left))) ∨
        functions.absorb (inputs.stateBefore (.fold right)) 20
            (workAbsorbPayload (.fold right) (inputs.nonce (.fold left))) ≠
          functions.absorb (inputs.stateBefore (.fold right)) 20
            (workAbsorbPayload (.fold right) (inputs.nonce (.fold right)))) := by
  constructor
  · exact hbinding (.fold left) (inputs.nonce (.fold right)) hvalues.symm
  · exact hbinding (.fold right) (inputs.nonce (.fold left)) hvalues

theorem substituting_distinct_batch_and_final_nonces_rejects_or_changes_states
    {State Challenge : Type*}
    {functions : ExecutableWorkFunctions State Challenge}
    {inputs : PositionedWorkInputs State Challenge}
    (hbinding : HashWorkTranscriptBinding functions inputs)
    (hvalues : inputs.nonce .batch ≠ inputs.nonce .finalQuery) :
    ((¬ functions.grindingOK (inputs.stateBefore .batch) 37
          (inputs.nonce .finalQuery)) ∨
        functions.absorb (inputs.stateBefore .batch) 28
            (workAbsorbPayload .batch (inputs.nonce .finalQuery)) ≠
          functions.absorb (inputs.stateBefore .batch) 28
            (workAbsorbPayload .batch (inputs.nonce .batch))) ∧
      ((¬ functions.grindingOK (inputs.stateBefore .finalQuery) 32
          (inputs.nonce .batch)) ∨
        functions.absorb (inputs.stateBefore .finalQuery) 5
            (workAbsorbPayload .finalQuery (inputs.nonce .batch)) ≠
          functions.absorb (inputs.stateBefore .finalQuery) 5
            (workAbsorbPayload .finalQuery (inputs.nonce .finalQuery))) := by
  constructor
  · exact hbinding .batch (inputs.nonce .finalQuery) hvalues.symm
  · exact hbinding .finalQuery (inputs.nonce .batch) hvalues

theorem rust_acceptance_projects_six_exact_steps_under_correspondence
    {State Challenge Digest : Type*}
    {rustAccepts : Prop}
    {rustHash : State → List Byte → Digest}
    {digestHasLeadingZeroBits : Digest → Nat → Prop}
    {rustFunctions : ExecutableWorkFunctions State Challenge}
    {inputs : PositionedWorkInputs State Challenge}
    (hcorrespondence : ExactRustWorkVerifierCorrespondence rustAccepts rustHash
      digestHasLeadingZeroBits rustFunctions inputs)
    (hrust : rustAccepts) :
    ∀ kind, ExactWorkOK rustFunctions inputs kind := by
  exact (hcorrespondence.acceptanceIffExactSixSteps.mp hrust).everyWorkOK

/-! ## Exactly-once event accounting -/

inductive CreditedWorkEvent where
  | polynomialBatchCollision
  | foldListFailure (round : Fin 4)
  | finalQueryMiss
  deriving DecidableEq, Fintype

def CreditedWorkEvent.workKind : CreditedWorkEvent → WorkKind
  | .polynomialBatchCollision => .batch
  | .foldListFailure round => .fold round
  | .finalQueryMiss => .finalQuery

def WorkKind.creditedEvent : WorkKind → CreditedWorkEvent
  | .batch => .polynomialBatchCollision
  | .fold round => .foldListFailure round
  | .finalQuery => .finalQueryMiss

theorem credited_event_work_left_inverse :
    Function.LeftInverse WorkKind.creditedEvent CreditedWorkEvent.workKind := by
  intro event
  cases event <;> rfl

theorem credited_event_work_right_inverse :
    Function.RightInverse WorkKind.creditedEvent CreditedWorkEvent.workKind := by
  intro kind
  cases kind <;> rfl

/-- Enumeration-only fact: the six *model* ledger constructors biject the six
model work positions.  It makes no claim that the deployed bad-event partition
has been mapped to these constructors. -/
theorem enumerated_work_events_biject_six_positions :
    Function.Bijective CreditedWorkEvent.workKind := by
  exact ⟨credited_event_work_left_inverse.injective,
    credited_event_work_right_inverse.surjective⟩

/-- Named applicability premise for the deployed bad-event partition.  Two
distinct actual events must not be credited to the same model ledger row. -/
def InjectiveActualWorkEventToLedger {ActualEvent : Type*}
    (toLedger : ActualEvent → CreditedWorkEvent) : Prop :=
  Function.Injective toLedger

/-- Separate coverage premise: every one of the six model rows is represented
by an actual event.  Injectivity and coverage are intentionally not inferred
from the model enumeration. -/
def CompleteActualWorkEventLedgerCoverage {ActualEvent : Type*}
    (toLedger : ActualEvent → CreditedWorkEvent) : Prop :=
  Function.Surjective toLedger

/-- Only after consuming the named actual-event injectivity and coverage seams
does exactly-once accounting transfer to the executable event partition. -/
theorem actual_event_correspondence_derives_exactly_once_accounting
    {ActualEvent : Type*} (toLedger : ActualEvent → CreditedWorkEvent)
    (hinjective : InjectiveActualWorkEventToLedger toLedger)
    (hcoverage : CompleteActualWorkEventLedgerCoverage toLedger) :
    Function.Bijective (fun event => (toLedger event).workKind) := by
  constructor
  · intro left right hequal
    apply hinjective
    exact enumerated_work_events_biject_six_positions.injective hequal
  · intro kind
    rcases enumerated_work_events_biject_six_positions.surjective kind with
      ⟨ledgerEvent, hkind⟩
    rcases hcoverage ledgerEvent with ⟨actualEvent, hevent⟩
    refine ⟨actualEvent, ?_⟩
    change (toLedger actualEvent).workKind = kind
    rw [hevent]
    exact hkind

def CreditedWorkEvent.bits (event : CreditedWorkEvent) : Nat :=
  event.workKind.difficulty

/-- A union ledger adds probabilities of alternative events.  It does not add
the six bit counts and present `2^-(37+34+33+30+25+32)` as one predicate. -/
noncomputable def AlternativeWorkEventSum
    (eventError : CreditedWorkEvent → ℝ) : ℝ :=
  ∑ event, eventError event

theorem alternative_event_union_bound_uses_each_event_once
    (unionError : ℝ) (eventError : CreditedWorkEvent → ℝ)
    (hUnion : unionError ≤ AlternativeWorkEventSum eventError)
    (hEach : ∀ event,
      eventError event ≤ 1 / 2 ^ event.bits) :
    unionError ≤ ∑ event : CreditedWorkEvent, (1 : ℝ) / 2 ^ event.bits := by
  calc
    unionError ≤ AlternativeWorkEventSum eventError := hUnion
    _ ≤ ∑ event : CreditedWorkEvent, (1 : ℝ) / 2 ^ event.bits := by
      exact Finset.sum_le_sum fun event _ => hEach event

/-! ## Width-19 batch arithmetic, with applicability kept explicit -/

def directCBatchWidth : Nat := 19
def powersBatchDegree (width : Nat) : Nat := width - 1

theorem direct_c_width19_powers_degree_is_18 :
    powersBatchDegree directCBatchWidth = 18 := by
  norm_num [powersBatchDegree, directCBatchWidth]

noncomputable def powersBatchArithmetic (coefficient : ℝ) : ℝ :=
  coefficient * ((21 / 2) / Real.sqrt (1 / 512))
    * ((2 * ((21 / 2) / Real.sqrt (1 / 512)) ^ 4 / 3) * (1 / 512) + 1)
    * 524288 / FIELD / 2 ^ 37

theorem width19_powers_batch_arithmetic_le_old_coefficient28 :
    powersBatchArithmetic 18 ≤ powersBatchArithmetic 28 := by
  let common : ℝ := ((21 / 2) / Real.sqrt (1 / 512))
    * ((2 * ((21 / 2) / Real.sqrt (1 / 512)) ^ 4 / 3) * (1 / 512) + 1)
    * 524288 / FIELD / 2 ^ 37
  have hcommon : 0 ≤ common := by
    dsimp [common]
    have hsqrt : (0 : ℝ) < Real.sqrt (1 / 512) :=
      Real.sqrt_pos.2 (by norm_num)
    have hfield : (0 : ℝ) < FIELD := FIELD_pos
    positivity
  have hmul : (18 : ℝ) * common ≤ 28 * common :=
    mul_le_mul_of_nonneg_right (by norm_num) hcommon
  calc
    powersBatchArithmetic 18 = 18 * common := by
      unfold powersBatchArithmetic common
      ring
    _ ≤ 28 * common := hmul
    _ = powersBatchArithmetic 28 := by
      unfold powersBatchArithmetic common
      ring

theorem width19_powers_batch_arithmetic_bound :
    powersBatchArithmetic 18 ≤ 1 / 2 ^ 107 := by
  apply le_trans width19_powers_batch_arithmetic_le_old_coefficient28
  simpa only [powersBatchArithmetic] using batch_bound

/-- Actual-schedule applicability seam.  Every schedule accepted by the v5
gate must satisfy all hypotheses of the cited width-19 polynomial-generator
MCA theorem.  This is deliberately separate from its numerical conclusion. -/
def ExactV5Width19DirectCBatchApplicability {Schedule : Type*}
    (acceptedSchedule citedMCAHypotheses : Schedule → Prop) : Prop :=
  ∀ schedule, acceptedSchedule schedule → citedMCAHypotheses schedule

/-- Published-theorem seam after all hypotheses are mapped.  It bounds the
actual schedule-indexed direct-C bad-event probability by the width-19
expression.  Lean does not manufacture this theorem from the arithmetic. -/
def CitedWidth19PowersBatchEventBound {Schedule : Type*}
    (citedMCAHypotheses : Schedule → Prop)
    (actualEventProbability : Schedule → ℝ) : Prop :=
  ∀ schedule, citedMCAHypotheses schedule →
    actualEventProbability schedule ≤ powersBatchArithmetic 18

theorem width19_batch_event_bound_of_applicability_and_cited_theorem
    {Schedule : Type*}
    (acceptedSchedule citedMCAHypotheses : Schedule → Prop)
    (actualEventProbability : Schedule → ℝ)
    (happlicability : ExactV5Width19DirectCBatchApplicability
      acceptedSchedule citedMCAHypotheses)
    (hcited : CitedWidth19PowersBatchEventBound
      citedMCAHypotheses actualEventProbability)
    (schedule : Schedule) (haccepted : acceptedSchedule schedule) :
    actualEventProbability schedule ≤ 1 / 2 ^ 107 := by
  exact (hcited schedule (happlicability schedule haccepted)).trans
    width19_powers_batch_arithmetic_bound

/-- Hostile regression tooth: the closed coefficient-18 arithmetic does not
imply that an accepted schedule satisfies the cited theorem's hypotheses. -/
theorem width19_arithmetic_does_not_supply_schedule_applicability :
    ∃ (acceptedSchedule citedMCAHypotheses : Bool → Prop),
      acceptedSchedule true ∧
        ¬ ExactV5Width19DirectCBatchApplicability
          acceptedSchedule citedMCAHypotheses := by
  refine ⟨fun _ => True, fun _ => False, trivial, ?_⟩
  intro happlicability
  exact happlicability true trivial

/-! ## Candidate serialized/public-message boundary ledger -/

/-- Candidate logical prover-message boundaries in the intended current v5
transcript.  Multiple challenges drawn without an intervening prover message
share one boundary.  Exact correspondence to Rust remains named below.

This finite type and its ordered trace describe serialization/transcript
position only.  They do not by themselves establish that any position is a
genuine public-coin IOP round to which the S-two/BCS theorem applies. -/
inductive V5PublicMessageBoundary where
  | c1RootAndPublicSalt
  | c2RootAndPublicSalt
  | maskedInitialClaim
  | semanticSumcheckRound (round : Fin 10)
  | terminalAndBatchWork
  | inactiveClaim
  | oodValue (round : Fin 4) (sample : Fin 2)
  | relationSumcheckAndFoldWork (round : Fin 4)
  | laterRootAndPublicSalt (layer : Fin 3)
  | finalPolynomialAndWork
  deriving DecidableEq, Fintype

theorem intended_v5_public_message_boundary_count_is_31 :
    Fintype.card V5PublicMessageBoundary = 31 := by
  decide

theorem intended_v5_public_message_boundary_count_le_32 :
    Fintype.card V5PublicMessageBoundary ≤ 32 := by
  rw [intended_v5_public_message_boundary_count_is_31]
  omega

/-- Exact ordered v5 trace.  OOD samples, relation/fold work and later roots
are interleaved exactly as in the executable four-round loop. -/
def intendedV5OrderedBoundaryTrace : List V5PublicMessageBoundary :=
  [.c1RootAndPublicSalt,
    .c2RootAndPublicSalt,
    .maskedInitialClaim,
    .semanticSumcheckRound 0,
    .semanticSumcheckRound 1,
    .semanticSumcheckRound 2,
    .semanticSumcheckRound 3,
    .semanticSumcheckRound 4,
    .semanticSumcheckRound 5,
    .semanticSumcheckRound 6,
    .semanticSumcheckRound 7,
    .semanticSumcheckRound 8,
    .semanticSumcheckRound 9,
    .terminalAndBatchWork,
    .inactiveClaim,
    .oodValue 0 0,
    .oodValue 0 1,
    .relationSumcheckAndFoldWork 0,
    .laterRootAndPublicSalt 0,
    .oodValue 1 0,
    .oodValue 1 1,
    .relationSumcheckAndFoldWork 1,
    .laterRootAndPublicSalt 1,
    .oodValue 2 0,
    .oodValue 2 1,
    .relationSumcheckAndFoldWork 2,
    .laterRootAndPublicSalt 2,
    .oodValue 3 0,
    .oodValue 3 1,
    .relationSumcheckAndFoldWork 3,
    .finalPolynomialAndWork]

theorem intended_v5_ordered_boundary_trace_length_is_31 :
    intendedV5OrderedBoundaryTrace.length = 31 := by
  decide

/-- Exact executable correspondence is equality of the decoded ordered trace,
not a cardinality-only bijection with an invented finite type. -/
def ExactRustV5OrderedBoundaryTraceCorrespondence {RustBoundary : Type*}
    (rustTrace : List RustBoundary)
    (decode : RustBoundary → V5PublicMessageBoundary) : Prop :=
  rustTrace.map decode = intendedV5OrderedBoundaryTrace

theorem rust_ordered_boundary_trace_length_le_32_of_exact_correspondence
    {RustBoundary : Type*} (rustTrace : List RustBoundary)
    (decode : RustBoundary → V5PublicMessageBoundary)
    (hcorrespondence :
      ExactRustV5OrderedBoundaryTraceCorrespondence rustTrace decode) :
    rustTrace.length ≤ 32 := by
  have hlength := congrArg List.length hcorrespondence
  simp only [List.length_map, intended_v5_ordered_boundary_trace_length_is_31]
    at hlength
  omega

/-- Numeric candidate accounting couples `R` to the length of that same
exactly decoded, ordered executable trace.  Here `R` is intended to be the IOP
round count in the S-two/BCS theorem, not an extractor factor or work factor.
This equality alone does not prove that the serialized positions are genuine
IOP rounds. -/
def ExactV5BCSBoundaryAccounting {RustBoundary : Type*}
    (R : ℝ) (rustTrace : List RustBoundary)
    (decode : RustBoundary → V5PublicMessageBoundary) : Prop :=
  ExactRustV5OrderedBoundaryTraceCorrespondence rustTrace decode ∧
    R = rustTrace.length

theorem bcs_R_meets_32_of_exact_ordered_boundary_accounting
    {RustBoundary : Type*} (R : ℝ) (rustTrace : List RustBoundary)
    (decode : RustBoundary → V5PublicMessageBoundary)
    (haccounting : ExactV5BCSBoundaryAccounting R rustTrace decode) :
    R ≤ R_BCS := by
  have hlength : rustTrace.length ≤ 32 :=
    rust_ordered_boundary_trace_length_le_32_of_exact_correspondence
      rustTrace decode haccounting.1
  rw [haccounting.2]
  norm_num [R_BCS] at hlength ⊢
  exact hlength

/-! ## S-two/BCS IOP-round semantic applicability -/

/-- Semantic obligations indexed by positions in the exact executable trace.
Each position must begin with public verifier randomness sampled after its
authenticated prefix, must contain the corresponding authenticated prover
oracle/message response, and must be covered by the claimed conditional
round-error bound.  Initial and final transcript material must also be
accounted for by the same IOP decomposition.

These predicates are an explicit Rust/protocol-to-IOP interface.  Byte-order
equality supplies none of them automatically. -/
structure STwoBCSIOPRoundSemantics {RustBoundary : Type*}
    (rustTrace : List RustBoundary) where
  verifierPublicCoinAfterAuthenticatedPrefix :
    Fin rustTrace.length → Prop
  authenticatedProverOracleOrMessageResponse :
    Fin rustTrace.length → Prop
  conditionalRoundErrorCovered : Fin rustTrace.length → Prop
  initialAndFinalTranscriptMaterialAccounted : Prop

/-- Exact semantic applicability required before using the S-two/BCS
bounded-query theorem.  `R` is the number of genuine public-coin IOP rounds,
not an extractor factor, work factor, random-oracle query count, or bare count
of serialized fields. -/
def STwoBCSIOPRoundSemanticApplicability {RustBoundary : Type*}
    (R : ℝ) (rustTrace : List RustBoundary)
    (semantics : STwoBCSIOPRoundSemantics rustTrace) : Prop :=
  R = rustTrace.length ∧
    1 ≤ R ∧
    semantics.initialAndFinalTranscriptMaterialAccounted ∧
    ∀ position,
      semantics.verifierPublicCoinAfterAuthenticatedPrefix position ∧
        semantics.authenticatedProverOracleOrMessageResponse position ∧
        semantics.conditionalRoundErrorCovered position

/-- Full v5 interface: exact candidate-trace accounting and independent
semantic proof that every counted position is a genuine S-two/BCS IOP round. -/
def ExactV5STwoBCSIOPRoundApplicability {RustBoundary : Type*}
    (R : ℝ) (rustTrace : List RustBoundary)
    (decode : RustBoundary → V5PublicMessageBoundary)
    (semantics : STwoBCSIOPRoundSemantics rustTrace) : Prop :=
  ExactV5BCSBoundaryAccounting R rustTrace decode ∧
    STwoBCSIOPRoundSemanticApplicability R rustTrace semantics

/-- Hostile regression tooth: an exactly ordered candidate byte/message trace
can still fail the genuine-IOP-round obligations at its first position. -/
theorem ordered_trace_correspondence_alone_does_not_imply_genuine_iop_rounds :
    ∃ semantics :
        STwoBCSIOPRoundSemantics intendedV5OrderedBoundaryTrace,
      ExactRustV5OrderedBoundaryTraceCorrespondence
          intendedV5OrderedBoundaryTrace id ∧
        ¬ STwoBCSIOPRoundSemanticApplicability 31
          intendedV5OrderedBoundaryTrace semantics := by
  let semantics :
      STwoBCSIOPRoundSemantics intendedV5OrderedBoundaryTrace :=
    { verifierPublicCoinAfterAuthenticatedPrefix := fun _ => False
      authenticatedProverOracleOrMessageResponse := fun _ => True
      conditionalRoundErrorCovered := fun _ => True
      initialAndFinalTranscriptMaterialAccounted := True }
  refine ⟨semantics, ?_, ?_⟩
  · simp [ExactRustV5OrderedBoundaryTraceCorrespondence]
  · intro happlicability
    have hfirst := happlicability.2.2.2
      (⟨0, by
        rw [intended_v5_ordered_boundary_trace_length_is_31]
        omega⟩ : Fin intendedV5OrderedBoundaryTrace.length)
    exact hfirst.1

/-- The capstone returns both facts needed by the endpoint: the numerical
bound on `R`, where `R` is the IOP round count, and the independent semantic
applicability fact.  It does not derive semantic applicability from ordered
trace correspondence. -/
theorem exact_v5_stwo_bcs_round_bound_and_semantic_applicability
    {RustBoundary : Type*} (R : ℝ) (rustTrace : List RustBoundary)
    (decode : RustBoundary → V5PublicMessageBoundary)
    (semantics : STwoBCSIOPRoundSemantics rustTrace)
    (happlicability :
      ExactV5STwoBCSIOPRoundApplicability R rustTrace decode semantics) :
    R ≤ 32 ∧
      STwoBCSIOPRoundSemanticApplicability R rustTrace semantics := by
  have hR : R ≤ R_BCS :=
    bcs_R_meets_32_of_exact_ordered_boundary_accounting
      R rustTrace decode happlicability.1
  exact ⟨by simpa [R_BCS] using hR, happlicability.2⟩

/-! ## Axiom audit -/

#print axioms exact_difficulty_map
#print axioms exact_label_and_stage_map
#print axioms work_kind_count_is_six
#print axioms exact_repaired_work_wire_offsets
#print axioms work_wire_regions_pairwise_disjoint
#print axioms relation_final_block_exact_coverage
#print axioms final_nonce_selector_exact_coverage
#print axioms fold_nonce_slots_exact_and_disjoint
#print axioms fold_nonce_slots_cover_exact_region
#print axioms distinct_fold_rounds_have_distinct_wire_slots
#print axioms swapping_fold_zero_and_one_changes_position
#print axioms batch_and_final_are_not_substitutable
#print axioms positioned_nonce_byte_offset_lt_fixed_body
#print axioms work_kind_nonce_slots_pairwise_disjoint
#print axioms positioned_nonce_byte_offset_injective
#print axioms positioned_nonce_bytes_biject_exact_48_wire_bytes
#print axioms positioned_nonce_byte_count_is_48
#print axioms positioned_nonce_runtime_offset_injective
#print axioms decode_encode_exact_le64
#print axioms encode_decode_exact_le64
#print axioms av5CUP08_is_exact_ascii
#print axioms model_project_recovers_work_wire_byte_for_byte
#print axioms model_parse_project_recovers_all_six_nonces_byte_for_byte
#print axioms rust_accepted_projection_recovers_all_six_nonces
#print axioms exact_work_absorb_payload_lengths
#print axioms fold_absorb_payload_is_round_then_le64
#print axioms batch_and_final_absorb_payloads_are_le64
#print axioms acceptance_projects_every_exact_work_ok
#print axioms acceptance_projects_batch_before_gamma
#print axioms acceptance_projects_each_fold_before_its_alpha
#print axioms acceptance_projects_final_before_selector
#print axioms honest_miner_and_exact_progression_imply_accepted
#print axioms changing_positioned_nonce_rejects_or_changes_post_state
#print axioms insufficient_work_at_any_position_rejects
#print axioms swapping_distinct_fold_nonces_rejects_or_changes_positioned_states
#print axioms substituting_distinct_batch_and_final_nonces_rejects_or_changes_states
#print axioms rust_acceptance_projects_six_exact_steps_under_correspondence
#print axioms credited_event_work_left_inverse
#print axioms credited_event_work_right_inverse
#print axioms enumerated_work_events_biject_six_positions
#print axioms actual_event_correspondence_derives_exactly_once_accounting
#print axioms alternative_event_union_bound_uses_each_event_once
#print axioms direct_c_width19_powers_degree_is_18
#print axioms width19_powers_batch_arithmetic_le_old_coefficient28
#print axioms width19_powers_batch_arithmetic_bound
#print axioms width19_batch_event_bound_of_applicability_and_cited_theorem
#print axioms width19_arithmetic_does_not_supply_schedule_applicability
#print axioms intended_v5_public_message_boundary_count_is_31
#print axioms intended_v5_public_message_boundary_count_le_32
#print axioms intended_v5_ordered_boundary_trace_length_is_31
#print axioms rust_ordered_boundary_trace_length_le_32_of_exact_correspondence
#print axioms bcs_R_meets_32_of_exact_ordered_boundary_accounting
#print axioms ordered_trace_correspondence_alone_does_not_imply_genuine_iop_rounds
#print axioms exact_v5_stwo_bcs_round_bound_and_semantic_applicability

end AspisV5NonceWorkAuthentication
