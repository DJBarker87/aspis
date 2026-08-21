import V5PrefixConcreteHelperJoin
import V5TranscriptRelationFinalJoin
import V5TranscriptTailUnchangedFinalJoin
import AspisFormal.V5TranscriptSourceAdapter

/-!
# Complete generated transcript projection

This file joins the three separately checked production pieces which affect
the accepted V5 transcript:

* the generated successful prefix call sequence and its six generated helper
  bodies;
* the unchanged generated four-round relation replay, including every byte
  window, fold nonce, later root, and public salt supplied to transcript
  helpers; and
* the unchanged generated final-polynomial, final-work, selector, and query
  tail.

`generatedRelationTrace` reports a maintained relation trace only when the
actual generated helper returns the exact byte-preserving event suffix proved
in `V5TranscriptRelationFinalJoin`.  It is therefore an execution projection,
not a second hand-written relation driver.

The result below is a statement about transcript calls and the values the
maintained driver exposes to later phases.  It adds no collision-resistance,
random-oracle, field-arithmetic, compiler, or Solana-runtime claim.
-/

namespace AspisV5TranscriptFullDriverJoin

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5NonceWorkAuthentication
open AspisV5TranscriptConnection
open AspisV5TranscriptSourceAdapter
open AspisV5TranscriptPrefixNormalizedGenerated
open AspisV5TranscriptPrefixExtractionBridge

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

abbrev PrefixFieldValue :=
  AspisV5PrefixConcreteHelperJoin.ExactFieldValue

def generatedPrefixTrace
    (input : V5TranscriptInputs)
    (outerCalls : List (PrefixExternalCall PrefixFieldValue))
    (workValid : Std.U64 → Std.U8 → Bool) : List TranscriptEvent :=
  runPrefixCalls
    (eventObserver
      (AspisV5PrefixConcreteHelperJoin.generatedPrefixHelpers input workValid))
    [] outerCalls

/-! The relation extraction has its own generated namespace.  Keep these
aliases explicit so importing the independently generated tail bundle cannot
silently select a similarly named Rust type. -/
abbrev RelationTranscript :=
  V5TranscriptRelationGenerated.aspis_core.transcript.Transcript

abbrev RelationParsed :=
  V5TranscriptRelationGenerated.v5_cu_probe.ParsedProbeData

/-- Project the actual generated relation execution to the maintained event
surface.  A successful result is accepted only if its exact event suffix is
byte-for-byte the source event projection. -/
def generatedRelationTrace
    (input : V5TranscriptInputs)
    (transcript : RelationTranscript)
    (parsed : RelationParsed) : List TranscriptEvent :=
  match
      V5TranscriptRelationGenerated.v5_cu_probe.replay_real_v5_relation_rounds
        transcript parsed with
  | .ok (.Ok result) =>
      if result.exactEvents = transcript.exactEvents ++
          AspisV5TranscriptRelationFinalJoin.exactSourceRelation input then
        sourceRelation input
      else
        []
  | _ => []

abbrev TailTranscript :=
  V5TranscriptTailUnchangedGenerated.aspis_core.transcript.Transcript

abbrev TailParsed :=
  V5TranscriptTailUnchangedGenerated.v5_cu_probe.ParsedProbeData

/-- Project the actual generated tail execution.  Failure contributes no
accepted trace; success contributes precisely the calls recorded by the
unchanged generated helper. -/
def generatedTailTrace
    (transcript : TailTranscript)
    (parsed : TailParsed)
    (selector : Std.U8) : List TranscriptEvent :=
  match
      V5TranscriptTailUnchangedGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
          transcript
          parsed selector with
  | .ok (.Ok _) =>
      List.flatMap
        AspisV5TranscriptTailUnchangedFinalJoin.expandTailEvent
        (AspisV5TranscriptTailUnchangedProof.expectedTailEvents parsed selector)
  | _ => []

/-- The three execution projections, in the same order as the production
driver. -/
def generatedProjectedTrace
    (input : V5TranscriptInputs)
    (outerCalls : List (PrefixExternalCall PrefixFieldValue))
    (workValid : Std.U64 → Std.U8 → Bool)
    (relationTranscript : RelationTranscript)
    (relationParsed : RelationParsed)
    (tailTranscript : TailTranscript)
    (tailParsed : TailParsed)
    (selector : Std.U8) : List TranscriptEvent :=
  generatedPrefixTrace input outerCalls workValid ++
    generatedRelationTrace input relationTranscript relationParsed ++
    generatedTailTrace tailTranscript tailParsed selector

/-- Package the checked execution projection with the values explicitly
forwarded by the maintained transcript interface. -/
def generatedProjectedDriver
    {PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues PrefixFieldValue PointValue)
    (outerCalls : List (PrefixExternalCall PrefixFieldValue))
    (workValid : Std.U64 → Std.U8 → Bool)
    (relationTranscript : RelationTranscript)
    (relationParsed : RelationParsed)
    (tailTranscript : TailTranscript)
    (tailParsed : TailParsed)
    (selector : Std.U8) :
    V5TranscriptDriverResult PrefixFieldValue PointValue where
  trace := generatedProjectedTrace input outerCalls workValid
    relationTranscript relationParsed tailTranscript tailParsed selector
  consumed := sourceShapedConsumption input derived

theorem generated_relation_trace_eq_source
    (input : V5TranscriptInputs)
    (transcript : RelationTranscript)
    (parsed : RelationParsed)
    (projection :
      AspisV5TranscriptRelationFinalJoin.ExactRelationParsedProjection
        input parsed) :
    generatedRelationTrace input transcript parsed = sourceRelation input := by
  unfold generatedRelationTrace
  rw [AspisV5TranscriptRelationFinalJoin.generated_helper_matches_exact_source_relation
      input transcript parsed projection]
  simp

theorem generated_tail_trace_eq_source
    (input : V5TranscriptInputs)
    (transcript : TailTranscript)
    (parsed : TailParsed)
    (selector : Std.U8)
    (polynomial :
      Array V5TranscriptTailUnchangedGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (hfinal :
      AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8
          parsed.v5_final_coefficients.val =
        bytes input.finalPolynomial)
    (hnonce :
      AspisV5TranscriptTailUnchangedFinalJoin.nonceOfU64
          parsed.v5_final_nonce = input.finalNonce)
    (hselector :
      AspisV5TranscriptTailUnchangedFinalJoin.byteOfU8 selector =
        input.selector)
    (success :
      V5TranscriptTailUnchangedGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
            transcript parsed selector = .ok (.Ok (polynomial, queries))) :
    generatedTailTrace transcript parsed selector = sourceTail input := by
  unfold generatedTailTrace
  rw [success]
  exact AspisV5TranscriptTailUnchangedFinalJoin.expected_tail_observation_maps_to_source
      input parsed selector
      hfinal hnonce hselector

/-- The complete generated execution projection is exactly the maintained
V5 transcript trace.  The relation parser proposition is the same proposition
now discharged by the independent unchanged `parse_probe_data` extraction;
there is no second relation-parser assumption in this join. -/
theorem generated_full_trace_eq_complete
    {PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues PrefixFieldValue PointValue)
    (values : PrefixSuccessfulValues PrefixFieldValue)
    (outerCalls : List (PrefixExternalCall PrefixFieldValue))
    (workValid : Std.U64 → Std.U8 → Bool)
    (hwork :
      workValid
        (AspisV5PrefixNonceEncodingProof.modelNonce input.batchNonce)
        37#u8 = true)
    (hclaim :
      AspisV5PrefixConcreteHelperJoin.ExactAcceptedInitialClaimEncoding
        input values)
    (outer :
      AspisV5PrefixConcreteHelperJoin.PinnedOuterSuccessfulPathBoundary
        outerCalls input derived values)
    (relationTranscript : RelationTranscript)
    (relationParsed : RelationParsed)
    (relationProjection :
      AspisV5TranscriptRelationFinalJoin.ExactRelationParsedProjection
        input relationParsed)
    (tailTranscript : TailTranscript)
    (tailParsed : TailParsed)
    (selector : Std.U8)
    (polynomial :
      Array V5TranscriptTailUnchangedGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (hfinal :
      AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8
          tailParsed.v5_final_coefficients.val =
        bytes input.finalPolynomial)
    (hnonce :
      AspisV5TranscriptTailUnchangedFinalJoin.nonceOfU64
          tailParsed.v5_final_nonce = input.finalNonce)
    (hselector :
      AspisV5TranscriptTailUnchangedFinalJoin.byteOfU8 selector =
        input.selector)
    (tailSuccess :
      V5TranscriptTailUnchangedGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
            tailTranscript tailParsed selector =
        .ok (.Ok (polynomial, queries))) :
    generatedProjectedTrace input outerCalls workValid relationTranscript
        relationParsed tailTranscript tailParsed selector =
      completeTranscriptTrace input := by
  have hprefix :
      generatedPrefixTrace input outerCalls
          workValid = sourcePrefix input := by
    exact AspisV5PrefixConcreteHelperJoin.checked_outer_prefix_trace_eq_source
        outerCalls input derived values
        workValid hwork hclaim outer
  have hrelation := generated_relation_trace_eq_source input
    relationTranscript relationParsed relationProjection
  have htail := generated_tail_trace_eq_source input tailTranscript tailParsed
    selector polynomial queries hfinal hnonce hselector tailSuccess
  rw [generatedProjectedTrace, hprefix, hrelation, htail]
  have hadapter := source_adapter_driver_is_exact input derived
  exact congrArg (fun result => result.trace) hadapter

/-- Driver-level form of `generated_full_trace_eq_complete`.  Its consumed
record is the maintained named-output projection; the companion tail theorem
below records the concrete generated polynomial and query return values. -/
theorem generated_projected_driver_eq_source
    {PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues PrefixFieldValue PointValue)
    (values : PrefixSuccessfulValues PrefixFieldValue)
    (outerCalls : List (PrefixExternalCall PrefixFieldValue))
    (workValid : Std.U64 → Std.U8 → Bool)
    (hwork :
      workValid
        (AspisV5PrefixNonceEncodingProof.modelNonce input.batchNonce)
        37#u8 = true)
    (hclaim :
      AspisV5PrefixConcreteHelperJoin.ExactAcceptedInitialClaimEncoding
        input values)
    (outer :
      AspisV5PrefixConcreteHelperJoin.PinnedOuterSuccessfulPathBoundary
        outerCalls input derived values)
    (relationTranscript : RelationTranscript)
    (relationParsed : RelationParsed)
    (relationProjection :
      AspisV5TranscriptRelationFinalJoin.ExactRelationParsedProjection
        input relationParsed)
    (tailTranscript : TailTranscript)
    (tailParsed : TailParsed)
    (selector : Std.U8)
    (polynomial :
      Array V5TranscriptTailUnchangedGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (hfinal :
      AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8
          tailParsed.v5_final_coefficients.val =
        bytes input.finalPolynomial)
    (hnonce :
      AspisV5TranscriptTailUnchangedFinalJoin.nonceOfU64
          tailParsed.v5_final_nonce = input.finalNonce)
    (hselector :
      AspisV5TranscriptTailUnchangedFinalJoin.byteOfU8 selector =
        input.selector)
    (tailSuccess :
      V5TranscriptTailUnchangedGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
            tailTranscript tailParsed selector =
        .ok (.Ok (polynomial, queries))) :
    generatedProjectedDriver input derived outerCalls workValid
        relationTranscript relationParsed tailTranscript tailParsed selector =
      sourceShapedTranscriptDriver input derived := by
  have htrace := generated_full_trace_eq_complete input derived values
    outerCalls workValid hwork hclaim outer relationTranscript relationParsed
    relationProjection tailTranscript tailParsed selector polynomial queries
    hfinal hnonce hselector tailSuccess
  exact congrArg
    (fun trace : List TranscriptEvent =>
      ({ trace := trace
         consumed := sourceShapedConsumption input derived } :
        V5TranscriptDriverResult PrefixFieldValue PointValue))
    htrace

/-- The same success used by the complete trace theorem also fixes the exact
generated return values: coefficients `[0,1,2,3]`, the 18 sampled queries,
and a selector in the accepted range. -/
theorem generated_full_tail_return_is_exact
    (input : V5TranscriptInputs)
    (transcript : TailTranscript)
    (parsed : TailParsed)
    (selector : Std.U8)
    (polynomial :
      Array V5TranscriptTailUnchangedGenerated.aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (hfinal :
      AspisV5TranscriptTailUnchangedFinalJoin.bytesOfU8
          parsed.v5_final_coefficients.val =
        bytes input.finalPolynomial)
    (hnonce :
      AspisV5TranscriptTailUnchangedFinalJoin.nonceOfU64
          parsed.v5_final_nonce = input.finalNonce)
    (hselector :
      AspisV5TranscriptTailUnchangedFinalJoin.byteOfU8 selector =
        input.selector)
    (success :
      V5TranscriptTailUnchangedGenerated.v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
            transcript parsed selector = .ok (.Ok (polynomial, queries))) :
    (polynomial.val = [0#usize, 1#usize, 2#usize, 3#usize] ∧
      queries.val = transcript.sampledQueries.val ∧
      transcript.sampledQueries.val.length = 18 ∧ selector.val < 3) ∧
      generatedTailTrace transcript parsed selector = sourceTail input := by
  have result := AspisV5TranscriptTailUnchangedFinalJoin.generated_tail_success_matches_source_tail
      input transcript parsed
      selector polynomial queries hfinal hnonce hselector success
  simpa [generatedTailTrace, success] using result

#print axioms generated_relation_trace_eq_source
#print axioms generated_tail_trace_eq_source
#print axioms generated_full_trace_eq_complete
#print axioms generated_projected_driver_eq_source
#print axioms generated_full_tail_return_is_exact

end AspisV5TranscriptFullDriverJoin
