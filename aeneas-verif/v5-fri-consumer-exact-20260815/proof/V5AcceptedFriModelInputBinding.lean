import V5FriGammaCanonical
import V5AcceptedEntryAlphaDecode
import V5AcceptedRemainingWorkBridge
import V5FriAcceptedForestChecks

/-!
# Accepted entry values used by the production FRI model

This file connects the values decoded by one successful accepted-entry run to
the duplicated types used by the focused FRI-consumer extraction.  Decoder
canonicality and gamma-combination canonicality are proved from executable
source translations; neither is supplied as a model premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5AcceptedFriModelInputBinding

open AspisV5AcceptedEntryAlphaDecode
open AspisV5AcceptedEntrySourceBridge
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriAcceptedForestChecks
open AspisV5FriArithmeticSemantics
open AspisV5FriConsumerValueSemantics
open AspisV5FriFoldSemantics
open AspisV5FriGammaCanonical
open AspisV5FriConsumerObservationBridge
open V5FriConsumerExact

abbrev EntryQM31 := V5AcceptedEntryGenerated.aspis_core.field.QM31
abbrev ConsumerQM31 := V5FriConsumerExact.aspis_core.field.QM31

private instance : Inhabited EntryQM31 :=
  ⟨{ c0 := { a := default, b := default },
     c1 := { a := default, b := default } }⟩

def entryToConsumerCM31
    (value : V5AcceptedEntryGenerated.aspis_core.field.CM31) :
    V5FriConsumerExact.aspis_core.field.CM31 :=
  { a := value.a, b := value.b }

def entryToConsumerQM31 (value : EntryQM31) : ConsumerQM31 :=
  { c0 := entryToConsumerCM31 value.c0,
    c1 := entryToConsumerCM31 value.c1 }

def entryArrayToConsumer {count : Std.Usize}
    (values : Array EntryQM31 count) : Array ConsumerQM31 count :=
  ⟨values.val.map entryToConsumerQM31, by simpa using values.property⟩

@[simp] theorem entry_generated_qm31ToConsumer_eq (value : EntryQM31) :
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.qm31ToConsumer value =
      entryToConsumerQM31 value :=
  rfl

theorem entry_generated_arrayToConsumer_eq {count : Std.Usize}
    (values : Array EntryQM31 count) :
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.consumerMapArray
        V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.qm31ToConsumer values =
      entryArrayToConsumer values := by
  apply Subtype.eq
  simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.consumerMapArray,
    entryArrayToConsumer]

@[simp] theorem entryToConsumerQM31_components (value : EntryQM31) :
    (entryToConsumerQM31 value).c0.a = value.c0.a ∧
    (entryToConsumerQM31 value).c0.b = value.c0.b ∧
    (entryToConsumerQM31 value).c1.a = value.c1.a ∧
    (entryToConsumerQM31 value).c1.b = value.c1.b := by
  exact ⟨rfl, rfl, rfl, rfl⟩

@[simp] theorem entryArrayToConsumer_values {count : Std.Usize}
    (values : Array EntryQM31 count) :
    (entryArrayToConsumer values).val = values.val.map entryToConsumerQM31 :=
  rfl

@[simp] theorem entryArrayToConsumer_entry4
    (values : Array EntryQM31 4#usize) (index : Fin 4) :
    (entryArrayToConsumer values).val[index.val]! =
      entryToConsumerQM31 values.val[index.val]! := by
  simp [entryArrayToConsumer, index.isLt]

/-- Both accepted-entry decoding and consumer decoding now transparently call
the same independent extraction of `QM31::from_le_bytes`. -/
theorem entry_from_le_bytes_success_is_consumer_success
    (bytes : Slice Std.U8) (value : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.aspis_core.field.QM31.from_le_bytes bytes =
        .ok (some value)) :
    V5FriConsumerExact.aspis_core.field.QM31.from_le_bytes bytes =
      .ok (some (entryToConsumerQM31 value)) := by
  unfold V5AcceptedEntryGenerated.aspis_core.field.QM31.from_le_bytes at success
  unfold V5FriConsumerExact.aspis_core.field.QM31.from_le_bytes
    V5FriConsumerExact.HelperTransport.fromLeBytes
  generalize hsource :
      V5FriByteDecoderSource.aspis_core.field.QM31.from_le_bytes bytes =
        sourceResult at success ⊢
  cases sourceResult with
  | fail error =>
      simp [hsource, V5FriConsumerExact.HelperTransport.mapResult] at success
  | div =>
      simp [hsource, V5FriConsumerExact.HelperTransport.mapResult] at success
  | ok decoded =>
      cases decoded with
      | none =>
          simp [hsource, V5FriConsumerExact.HelperTransport.mapResult] at success
      | some decoded =>
          simp only [hsource, V5FriConsumerExact.HelperTransport.mapResult,
            Option.map] at success ⊢
          have hvalue : value = {
              c0 := { a := decoded.c0.a, b := decoded.c0.b },
              c1 := { a := decoded.c1.a, b := decoded.c1.b } } := by
            exact Option.some.inj (Result.ok.inj success).symm
          subst value
          rfl

theorem entry_from_le_bytes_success_canonical
    (bytes : Slice Std.U8) (value : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.aspis_core.field.QM31.from_le_bytes bytes =
        .ok (some value)) :
    canonicalQM31 (toExactQM31 (entryToConsumerQM31 value)) := by
  exact consumer_decode_success_canonical bytes (entryToConsumerQM31 value)
    (entry_from_le_bytes_success_is_consumer_success bytes value success)

/-- A successful source-level indexed decoder call must have obtained its
value from the executable byte decoder.  This is an inversion of the actual
translated `decode_qm31`, not a decoder assumption. -/
theorem entry_decode_qm31_success_from_le_bytes
    (bytes : Slice Std.U8) (index : Std.Usize) (value : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31 bytes index =
        .ok (.Ok value)) :
    ∃ selected : Slice Std.U8,
      V5AcceptedEntryGenerated.aspis_core.field.QM31.from_le_bytes selected =
        .ok (some value) := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31 at success
  generalize hmul :
      Usize.checked_mul index
        V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES = mulResult at success
  cases mulResult with
  | none =>
    simp [Std.lift, V5AcceptedEntryGenerated.core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame, core.convert.FromSame.from] at success
  | some offset =>
      simp only [Std.lift,
        V5AcceptedEntryGenerated.core.option.Option.ok_or,
        bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch]
        at success
      generalize hadd :
          offset + V5AcceptedEntryGenerated.v5_cu_probe.QM31_BYTES =
            endResult at success
      cases endResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
      | div => simp [Bind.bind, Aeneas.Std.bind] at success
      | ok finish =>
        simp only [bind_tc_ok] at success
        generalize hslice :
            core.slice.Slice.get
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
              bytes { start := offset, «end» := finish } =
              sliceResult at success
        cases sliceResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
        | div => simp [Bind.bind, Aeneas.Std.bind] at success
        | ok selectedOption =>
          cases selectedOption with
          | none =>
            simp [V5AcceptedEntryGenerated.core.option.Option.ok_or,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame, core.convert.FromSame.from] at success
          | some selected =>
            simp only [V5AcceptedEntryGenerated.core.option.Option.ok_or,
              bind_tc_ok,
              core.result.Result.Insts.CoreOpsTry.branch]
              at success
            generalize hdecode :
                V5AcceptedEntryGenerated.aspis_core.field.QM31.from_le_bytes
                  selected = decodeResult at success
            cases decodeResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
            | div => simp [Bind.bind, Aeneas.Std.bind] at success
            | ok decodedOption =>
              cases decodedOption with
              | none =>
                simp [V5AcceptedEntryGenerated.core.option.Option.ok_or]
                  at success
              | some decoded =>
                simp only [bind_tc_ok,
                  V5AcceptedEntryGenerated.core.option.Option.ok_or]
                  at success
                have hvalue : decoded = value := by
                  exact core.result.Result.Ok.inj (Result.ok.inj success)
                subst value
                exact ⟨selected, hdecode⟩

theorem entry_decode_qm31_success_canonical
    (bytes : Slice Std.U8) (index : Std.Usize) (value : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31 bytes index =
        .ok (.Ok value)) :
    canonicalQM31 (toExactQM31 (entryToConsumerQM31 value)) := by
  obtain ⟨selected, hdecode⟩ :=
    entry_decode_qm31_success_from_le_bytes bytes index value success
  exact entry_from_le_bytes_success_canonical selected value hdecode

/-- The four alpha values returned by the accepted entry decoder all have
canonical field representatives. -/
theorem decoded_entry_alphas_are_canonical
    (parsed : AspisV5AcceptedEntryAlphaDecode.Parsed)
    (output : Array EntryQM31 4#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.decode_v5_fri_alphas parsed =
        .ok (.Ok output)) :
    CanonicalQM31Array4
      (mapArray toExactQM31 (entryArrayToConsumer output)) := by
  obtain ⟨a0, a1, a2, a3, h0, h1, h2, h3, hvalues⟩ :=
    decode_v5_fri_alphas_success_calls parsed output success
  have hc0 := entry_decode_qm31_success_canonical
    parsed.relation_alphas 0#usize a0 h0
  have hc1 := entry_decode_qm31_success_canonical
    parsed.relation_alphas 1#usize a1 h1
  have hc2 := entry_decode_qm31_success_canonical
    parsed.relation_alphas 2#usize a2 h2
  have hc3 := entry_decode_qm31_success_canonical
    parsed.relation_alphas 3#usize a3 h3
  intro index hindex
  interval_cases index <;>
    simp [mapArray, entryArrayToConsumer, hvalues, hc0, hc1, hc2, hc3]

/-- The final polynomial returned by the accepted selected-query driver has
canonical field representatives.  The four decoder calls and their value
equality come from that same successful driver execution. -/
theorem selected_entry_final_polynomial_is_canonical
    (transcript : AspisV5AcceptedEntrySourceBridge.EntryTranscript)
    (parsed : AspisV5AcceptedEntrySourceBridge.EntryParsed)
    (point : Array EntryQM31 10#usize)
    (polynomial : Array EntryQM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.derive_v5_selected_good_queries_from_transcript
          transcript parsed point = .ok (.Ok (polynomial, queries))) :
    CanonicalQM31Array4
      (mapArray toExactQM31 (entryArrayToConsumer polynomial)) := by
  obtain ⟨q0, q1, q2, q3, h0, h1, h2, h3, hvalues⟩ :=
    selected_query_success_has_decoded_polynomial transcript parsed point
      polynomial queries success
  have hc0 := entry_decode_qm31_success_canonical
    parsed.v5_final_coefficients 0#usize q0 h0
  have hc1 := entry_decode_qm31_success_canonical
    parsed.v5_final_coefficients 1#usize q1 h1
  have hc2 := entry_decode_qm31_success_canonical
    parsed.v5_final_coefficients 2#usize q2 h2
  have hc3 := entry_decode_qm31_success_canonical
    parsed.v5_final_coefficients 3#usize q3 h3
  intro index hindex
  interval_cases index <;>
    simp [mapArray, entryArrayToConsumer, hvalues, hc0, hc1, hc2, hc3]

abbrev EntryOpenings :=
  V5AcceptedEntryGenerated.v5_cu_probe.private_openings.VerifiedV5PrivateOpenings
abbrev EntryPrepared :=
  V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims
abbrev EntrySink :=
  V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.V5FriCheckSink

/-- A successful combined-entry FRI call is a successful call of the focused
consumer translation.  This is inversion of the explicit namespace adapter
in the normalized generated entry, not a call-equality premise. -/
theorem entry_fri_success_builds_accepted_consumer_call
    (openings : EntryOpenings) (prepared : EntryPrepared)
    (alphas finalPolynomial : Array EntryQM31 4#usize)
    (sink : EntrySink)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.check_v5_fri_queries
          openings prepared alphas finalPolynomial
          V5AcceptedEntryGenerated.aspis_core.field.M31.inv =
        .ok (.Ok sink)) :
    ∃ acceptedCall : AcceptedFriCall,
      acceptedCall.openings =
          V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.openingsToConsumer
            openings ∧
      acceptedCall.prepared =
          V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedClaimsToConsumer
            prepared ∧
      acceptedCall.alphas = entryArrayToConsumer alphas ∧
      acceptedCall.finalPolynomial = entryArrayToConsumer finalPolynomial ∧
      acceptedCall.inverse =
          V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.inverseToConsumer
            V5AcceptedEntryGenerated.aspis_core.field.M31.inv := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.check_v5_fri_queries
    at success
  generalize hconsumer :
      V5FriConsumerExact.fri_checks.check_v5_fri_queries
        (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.openingsToConsumer
          openings)
        (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedClaimsToConsumer
          prepared)
        (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.consumerMapArray
          V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.qm31ToConsumer
          alphas)
        (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.consumerMapArray
          V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.qm31ToConsumer
          finalPolynomial)
        (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.inverseToConsumer
          V5AcceptedEntryGenerated.aspis_core.field.M31.inv) = consumerResult
      at success
  cases consumerResult with
  | fail error => simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.resultFromConsumer] at success
  | div => simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.resultFromConsumer] at success
  | ok inner =>
      cases inner with
      | Err error =>
          simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.resultFromConsumer]
            at success
      | Ok consumerSink =>
          rw [entry_generated_arrayToConsumer_eq alphas,
            entry_generated_arrayToConsumer_eq finalPolynomial] at hconsumer
          refine ⟨{
            openings :=
              V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.openingsToConsumer
                openings
            prepared :=
              V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedClaimsToConsumer
                prepared
            alphas := entryArrayToConsumer alphas
            finalPolynomial := entryArrayToConsumer finalPolynomial
            inverse :=
              V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.inverseToConsumer
                V5AcceptedEntryGenerated.aspis_core.field.M31.inv
            sink := consumerSink
            accepted := ?_ }, rfl, rfl, rfl, rfl, rfl⟩
          exact hconsumer

#print axioms entry_from_le_bytes_success_is_consumer_success
#print axioms entry_from_le_bytes_success_canonical
#print axioms entry_decode_qm31_success_from_le_bytes
#print axioms entry_decode_qm31_success_canonical
#print axioms decoded_entry_alphas_are_canonical
#print axioms selected_entry_final_polynomial_is_canonical
#print axioms entry_fri_success_builds_accepted_consumer_call

end AspisV5AcceptedFriModelInputBinding
