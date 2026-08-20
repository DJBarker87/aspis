import V5FriConsumerEndToEndProof
import AspisFormal.V5FriSourceLoopOrder

/-!
# Adapter from the extracted FRI consumer to the maintained observation model

The maintained model deliberately leaves `rustObservation` abstract.  This
module supplies the concrete adapter for the unchanged extracted
`check_v5_fri_queries`: an observation is produced only together with a proof
that the generated top-level function accepted.  Its driver fields are direct
conversions of the returned Rust opening views and index vectors, and its read
schedule is the literal source-shaped four-loop schedule.

`accepted_resolver_has_complete_source_execution` separately proves that each
such observation has the exact production execution evidence: all four loops
ran and every enumerated query performed its source accessor calls.  Thus the
read-trace equality below is an adapter theorem, not a new FRI assumption.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 3000

namespace AspisV5FriConsumerObservationBridge

open V5FriConsumerExact
open AspisV5FriConsumerExactProof
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleConsumedValueBridge
open AspisV5FriSourceLoopOrder

def generatedU8ToByte (byte : Std.U8) :
    AspisV5MerkleAuthenticationBinding.Byte :=
  ⟨byte.val, byte.lt_succ_max⟩

def generatedOpeningToReturned (opening : Opening) : ReturnedOpening where
  count := opening.count.val
  valueWidth := opening.value_width.val
  records := opening.records.val.map generatedU8ToByte
  frontier := opening.frontier.val.map generatedU8ToByte
  offsets :=
    { count := opening.offsets.count.val
      records := opening.offsets.records.val
      frontierCount := opening.offsets.frontier_count.val
      frontier := opening.offsets.frontier.val
      endOffset := opening.offsets.end.val }

def generatedIndicesToNat (indices : alloc.vec.Vec Std.U32) : List Nat :=
  indices.val.map (fun index => index.val)

private theorem later_length (openings : VerifiedOpenings) :
    openings.later.val.length = 3 := by
  simpa using Aeneas.Std.Array.length_eq openings.later

private theorem later_indices_length (openings : VerifiedOpenings) :
    openings.indices.later.val.length = 3 := by
  simpa using Aeneas.Std.Array.length_eq openings.indices.later

def generatedDriverOutput (openings : VerifiedOpenings) : V5DriverOutput where
  c1 := generatedOpeningToReturned openings.c1
  c2 := generatedOpeningToReturned openings.c2
  line1 := generatedOpeningToReturned
    (openings.later.val.get ⟨0, by rw [later_length]; omega⟩)
  line2 := generatedOpeningToReturned
    (openings.later.val.get ⟨1, by rw [later_length]; omega⟩)
  line3 := generatedOpeningToReturned
    (openings.later.val.get ⟨2, by rw [later_length]; omega⟩)
  layer0Indices := generatedIndicesToNat openings.indices.layer0
  line1Indices := generatedIndicesToNat
    (openings.indices.later.val.get
      ⟨0, by rw [later_indices_length]; omega⟩)
  line2Indices := generatedIndicesToNat
    (openings.indices.later.val.get
      ⟨1, by rw [later_indices_length]; omega⟩)
  line3Indices := generatedIndicesToNat
    (openings.indices.later.val.get
      ⟨2, by rw [later_indices_length]; omega⟩)
  bytesConsumed := openings.bytes_consumed.val
  remainder := []

/-- All inputs to one successful extracted FRI call.  The equality field is
the result of evaluating the unchanged generated top-level function. -/
structure AcceptedFriCall where
  openings : VerifiedOpenings
  prepared : fri_checks.V5PreparedPcsClaims
  alphas : Array aspis_core.field.QM31 4#usize
  finalPolynomial : Array aspis_core.field.QM31 4#usize
  inverse : aspis_core.field.M31 → aspis_core.field.M31
  sink : fri_checks.V5FriCheckSink
  accepted : fri_checks.check_v5_fri_queries openings prepared alphas
    finalPolynomial inverse = .ok (.Ok sink)

def AcceptedFriCall.observation (call : AcceptedFriCall) :
    OpeningAndFriObservation :=
  let driver := generatedDriverOutput call.openings
  { driver
    friReads := sourceShapedFriReadSchedule driver }

/-- A production wrapper may resolve a high-level call to the prepared Rust
arguments only when parsing, preparation, and the extracted FRI check all
succeed.  The parser equality remains a separate proof, as intended by the
maintained split theorem. -/
def observationFromAcceptedResolver
    (resolve : AspisV5MerkleRustBridge.V5ProductionCall →
      Option AcceptedFriCall) :
    AspisV5MerkleRustBridge.V5ProductionCall →
      Option OpeningAndFriObservation :=
  fun call => (resolve call).map AcceptedFriCall.observation

/-- The concrete successful-call adapter discharges the maintained FRI read
trace boundary by construction from the exact source-shaped schedule. -/
theorem accepted_resolver_read_trace_equality
    (resolve : AspisV5MerkleRustBridge.V5ProductionCall →
      Option AcceptedFriCall) :
    CheckV5FriQueriesSuccessfulReadTraceEquality
      (observationFromAcceptedResolver resolve) := by
  intro call observation hresolve
  unfold observationFromAcceptedResolver at hresolve
  cases hcall : resolve call with
  | none => simp [hcall] at hresolve
  | some acceptedCall =>
    simp only [hcall, Option.map_some, Option.some.injEq] at hresolve
    subst observation
    rfl

/-- Every value admitted by the adapter has the complete unchanged-source
execution proof, including one exact production read witness for every query
position in all four loops. -/
theorem accepted_resolver_has_complete_source_execution
    (resolve : AspisV5MerkleRustBridge.V5ProductionCall →
      Option AcceptedFriCall)
    (call : AspisV5MerkleRustBridge.V5ProductionCall)
    (acceptedCall : AcceptedFriCall)
    (_hresolve : resolve call = some acceptedCall) :
    Nonempty (AcceptedProductionFriExecution acceptedCall.openings
      acceptedCall.prepared acceptedCall.finalPolynomial acceptedCall.sink) :=
  unchanged_source_acceptance_yields_complete_fri_execution
    acceptedCall.openings acceptedCall.prepared acceptedCall.alphas
    acceptedCall.finalPolynomial acceptedCall.inverse acceptedCall.sink
    acceptedCall.accepted

/-- With the existing parser-output theorem, the concrete accepted-call
adapter yields the maintained combined parser-and-FRI source equality.  No
independent FRI-loop trace premise remains. -/
theorem opening_parser_and_accepted_resolver_imply_consumer_equality
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (resolve : AspisV5MerkleRustBridge.V5ProductionCall →
      Option AcceptedFriCall)
    (hparser : ExactRustV5OpeningParserOutputEquality sha256
      (observationFromAcceptedResolver resolve)) :
    ExactRustV5OpeningAndFriConsumerEquality sha256
      (observationFromAcceptedResolver resolve) :=
  openingParser_and_checkV5FriQueriesReadTrace_imply_consumerEquality sha256
    (observationFromAcceptedResolver resolve) hparser
    (accepted_resolver_read_trace_equality resolve)

#print axioms accepted_resolver_read_trace_equality
#print axioms accepted_resolver_has_complete_source_execution
#print axioms opening_parser_and_accepted_resolver_imply_consumer_equality

end AspisV5FriConsumerObservationBridge
