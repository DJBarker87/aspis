import AspisFormal.V5TranscriptPrefixNormalizedGenerated

/-!
# Checked bridge for the extracted V5 transcript prefix

The pinned Aeneas function calls transcript primitives and several larger
helpers through opaque external declarations.  Therefore its generated Lean
term cannot itself expose a transcript trace.

This file interprets the mechanically checked successful-path normalization.
Direct absorbs and challenges are observed without assumptions. The six
larger helpers are explicit observations supplied by `PrefixHelperEvents`.
Separate source proofs now establish all six helper bodies from unchanged
Rust. If those observations match their maintained models on the accepted
arguments, the extracted prefix has exactly `sourcePrefix`'s event order and
payloads. This file deliberately keeps the observation interface visible
rather than turning external generated declarations into hidden axioms.

The terminal-context and returned-value theorems are unconditional facts
about the checked normalized dataflow.  Nothing here adds a SHA-256,
Fiat--Shamir, sampler-success, compiler, or translation security claim.
-/

namespace AspisV5TranscriptPrefixExtractionBridge

open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5NonceWorkAuthentication
open AspisV5TranscriptConnection
open AspisV5TranscriptSourceAdapter
open AspisV5TranscriptPrefixNormalizedGenerated

/-! ## Parameterized observations of external calls -/

/-- An observer for the external calls retained by the normalization. -/
structure PrefixExternalObserver (State FieldValue : Type*) where
  absorb :
    State → AbsorbSlot → Byte → List Byte → State
  absorbRoundRoot :
    State → Fin 4 → List Byte → List Byte → State
  challengeQm31 :
    State → SqueezeSlot → FieldValue → State
  absorbC2Root :
    State → List Byte → List Byte → State
  beginZerocheck :
    State → FieldValue → (Fin 10 → FieldValue) → FieldValue → State
  beginMaskedSumcheck :
    State → FieldValue → FieldValue → State
  verifySemanticSumcheck :
    State → List Byte → FieldValue → (Fin 10 → FieldValue) →
      FieldValue → State
  checkAndAbsorbBatchNonce :
    State → Nonce64 → State
  challengeNonzeroQm31 :
    State → SqueezeSlot → FieldValue → State

def observePrefixCall
    {State FieldValue : Type*}
    (observer : PrefixExternalObserver State FieldValue) :
    State → PrefixExternalCall FieldValue → State
  | state, .absorb slot label payload =>
      observer.absorb state slot label payload
  | state, .absorbRoundRoot round root salt =>
      observer.absorbRoundRoot state round root salt
  | state, .challengeQm31 slot result =>
      observer.challengeQm31 state slot result
  | state, .absorbC2Root root salt =>
      observer.absorbC2Root state root salt
  | state, .beginZerocheck theta point mu =>
      observer.beginZerocheck state theta point mu
  | state, .beginMaskedSumcheck initialClaim eta =>
      observer.beginMaskedSumcheck state initialClaim eta
  | state, .verifySemanticSumcheck wire initialClaim challenges terminalClaim =>
      observer.verifySemanticSumcheck state wire initialClaim challenges
        terminalClaim
  | state, .checkAndAbsorbBatchNonce nonce =>
      observer.checkAndAbsorbBatchNonce state nonce
  | state, .challengeNonzeroQm31 slot result =>
      observer.challengeNonzeroQm31 state slot result

def runPrefixCalls
    {State FieldValue : Type*}
    (observer : PrefixExternalObserver State FieldValue)
    (initial : State) (calls : List (PrefixExternalCall FieldValue)) : State :=
  calls.foldl (observePrefixCall observer) initial

/-- Event traces supplied for helpers that the prefix extraction left opaque.
Each function receives all arguments retained from the generated call. -/
structure PrefixHelperEvents (FieldValue : Type*) where
  absorbRoundRoot :
    Fin 4 → List Byte → List Byte → List TranscriptEvent
  absorbC2Root :
    List Byte → List Byte → List TranscriptEvent
  beginZerocheck :
    FieldValue → (Fin 10 → FieldValue) → FieldValue →
      List TranscriptEvent
  beginMaskedSumcheck :
    FieldValue → FieldValue → List TranscriptEvent
  verifySemanticSumcheck :
    List Byte → FieldValue → (Fin 10 → FieldValue) → FieldValue →
      List TranscriptEvent
  checkAndAbsorbBatchNonce :
    Nonce64 → List TranscriptEvent

def eventObserver {FieldValue : Type*}
    (helpers : PrefixHelperEvents FieldValue) :
    PrefixExternalObserver (List TranscriptEvent) FieldValue where
  absorb state slot label payload :=
    state ++ [.absorb slot label payload]
  absorbRoundRoot state round root salt :=
    state ++ helpers.absorbRoundRoot round root salt
  challengeQm31 state slot _ :=
    state ++ [.squeeze slot]
  absorbC2Root state root salt :=
    state ++ helpers.absorbC2Root root salt
  beginZerocheck state theta point mu :=
    state ++ helpers.beginZerocheck theta point mu
  beginMaskedSumcheck state initialClaim eta :=
    state ++ helpers.beginMaskedSumcheck initialClaim eta
  verifySemanticSumcheck state wire initialClaim challenges terminalClaim :=
    state ++ helpers.verifySemanticSumcheck wire initialClaim challenges
      terminalClaim
  checkAndAbsorbBatchNonce state nonce :=
    state ++ helpers.checkAndAbsorbBatchNonce nonce
  challengeNonzeroQm31 state slot _ :=
    state ++ [.squeeze slot]

def generatedSuccessfulPrefixTrace
    {FieldValue PointValue : Type*}
    (helpers : PrefixHelperEvents FieldValue)
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue)
    (values : PrefixSuccessfulValues FieldValue) : List TranscriptEvent :=
  runPrefixCalls (eventObserver helpers) []
    (generatedSuccessfulPrefixCalls input derived values)

/-! ## Explicit helper interface -/

/-- Exactly what must be established about the helper bodies that were opaque
in this Aeneas extraction.  The predicate mentions only the arguments used by
the successful generated call sequence; it makes no universal claim about
other inputs or rejection paths. -/
structure ExactSuccessfulPrefixHelperEvents
    {FieldValue PointValue : Type*}
    (helpers : PrefixHelperEvents FieldValue)
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue)
    (values : PrefixSuccessfulValues FieldValue) : Prop where
  roundRoot :
    helpers.absorbRoundRoot 0 (bytes (input.circleRoot 0))
        (bytes (input.publicSalt 0)) =
      [sourceAbsorb input (.circleRoot 0)]
  c2Root :
    helpers.absorbC2Root (bytes input.c2Root) (bytes (input.publicSalt 1)) =
      [sourceAbsorb input .c2Root]
  zerocheck :
    helpers.beginZerocheck derived.theta derived.zerocheckPoint derived.mu =
      [sourceAbsorb input .constraintRegistry,
        sourceAbsorb input .helperSum,
        sourceSqueeze .theta] ++
      List.ofFn (fun coordinate : Fin 10 =>
        sourceSqueeze (.zerocheckPoint coordinate)) ++
      [sourceSqueeze .mu]
  maskedSumcheck :
    helpers.beginMaskedSumcheck values.initialClaim derived.eta =
      [sourceAbsorb input .maskClaim, sourceSqueeze .eta]
  semanticSumcheck :
    helpers.verifySemanticSumcheck (semanticSumcheckWire input)
        values.initialClaim derived.relationChallenge values.terminalClaim =
      (List.ofFn (sourceSemanticRound input)).flatten
  batchNonce :
    helpers.checkAndAbsorbBatchNonce input.batchNonce =
      sourceCheckAndAbsorb input .batch

/-- Subject only to the explicit helper observations above, the checked
normalized successful path has exactly the maintained prefix event trace.
Direct absorb labels/payloads and all challenge positions are consequences of
the normalized program, not fields of the helper premise. -/
theorem normalized_generated_successful_prefix_trace_eq_sourcePrefix
    {FieldValue PointValue : Type*}
    (helpers : PrefixHelperEvents FieldValue)
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue)
    (values : PrefixSuccessfulValues FieldValue)
    (hexact : ExactSuccessfulPrefixHelperEvents helpers input derived values) :
    generatedSuccessfulPrefixTrace helpers input derived values =
      sourcePrefix input := by
  rcases hexact with ⟨hroot, hc2, hzero, hmask, hsumcheck, hbatch⟩
  simp [generatedSuccessfulPrefixTrace, generatedSuccessfulPrefixCalls,
    runPrefixCalls, observePrefixCall, eventObserver, hroot, hc2, hzero, hmask,
    hsumcheck, hbatch, sourcePrefix, sourceAbsorb, sourceSqueeze,
    absorbPayload]

theorem normalized_generated_successful_prefix_trace_eq_typed_schedule
    {FieldValue PointValue : Type*}
    (helpers : PrefixHelperEvents FieldValue)
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue)
    (values : PrefixSuccessfulValues FieldValue)
    (hexact : ExactSuccessfulPrefixHelperEvents helpers input derived values) :
    generatedSuccessfulPrefixTrace helpers input derived values =
      prefixSchedule.map (realizeStep input) := by
  rw [normalized_generated_successful_prefix_trace_eq_sourcePrefix
    helpers input derived values hexact, source_prefix_is_exact]

/-! ## Checked successful-value flow -/

/-- The terminal context uses the six named values returned earlier by the
normalized successful branch. -/
theorem normalized_terminal_context_uses_exact_challenges
    {FieldValue PointValue : Type*}
    (derived : V5DerivedValues FieldValue PointValue) :
    let context := generatedTerminalContext derived
    context.lambda = derived.lambda ∧
      context.chi = derived.chi ∧
      context.theta = derived.theta ∧
      context.zerocheckPoint = derived.zerocheckPoint ∧
      context.mu = derived.mu ∧
      context.eta = derived.eta := by
  simp [generatedTerminalContext]

/-- The accepted return forwards eta, the ten semantic-round challenges,
gamma, kappa, and the four decoded claims under their generated names. -/
theorem normalized_successful_return_uses_exact_values
    {FieldValue PointValue : Type*}
    (derived : V5DerivedValues FieldValue PointValue)
    (values : PrefixSuccessfulValues FieldValue) :
    let result := generatedPrefixReturn derived values
    result.eta = derived.eta ∧
      result.roundChallenges = derived.relationChallenge ∧
      result.gamma = derived.gamma ∧
      result.kappa = derived.kappa ∧
      result.terminalReal = values.terminalReal ∧
      result.terminalMask = values.terminalMask ∧
      result.terminalMasked = values.terminalMasked ∧
      result.inactiveClaim = values.inactiveClaim := by
  simp [generatedPrefixReturn]

#print axioms normalized_generated_successful_prefix_trace_eq_sourcePrefix
#print axioms normalized_generated_successful_prefix_trace_eq_typed_schedule
#print axioms normalized_terminal_context_uses_exact_challenges
#print axioms normalized_successful_return_uses_exact_values

end AspisV5TranscriptPrefixExtractionBridge
