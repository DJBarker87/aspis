import V7Tag73FixedFieldLayoutModel

/-!
# Source-facing Tag-73 fixed-field capstone interface

This file isolates the conclusion that must be constructed by inversion of
the translated production caller.  It deliberately does not postulate a
Rust/Lean agreement proposition.  `ExactSourceFixedFieldTrace` is output data:
the future generated-source theorem must construct it from the literal
success equation for
`v7_verifier.verify_v7_read_only_with_statement_digest`.

The trace contains only facts exposed by translated control flow:

* the exact parser length, cap, prefix bytes, and padding check;
* strict limb comparisons from all 641 successful `next_qm31` calls; and
* the seven typed storage projections in frozen global-field order.

The public generated-source theorem must not accept this trace, canonicality,
decoder success, or stored-view equality as a premise.  It accepts only the
literal generated caller-success equation and constructs this trace before
applying `exactSourceFixedFieldTrace_constructs_capstone` below.
-/

set_option autoImplicit false

namespace AspisV7Tag73FixedFieldSourceCapstone

open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73CurrentSourceDecodeBridge
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact
open AspisV6TranscriptRelationGrammar
open AspisV6AcceptedPathObligations
open AspisV7Tag73FixedFieldLayoutModel

/-- Exact fixed-field information constructed from translated successful
control flow.  This is a `Type`, not an assumed proposition, so later source
proofs may retain the concrete packed section and stored values without
choice or large elimination from `Prop`.

`packedPrefix` is intentionally only a byte identity.  It does not state
canonicality or decoding: those are separately derived from the reader's
strict comparisons and recorded in `canonical`.
-/
structure ExactSourceFixedFieldTrace
    (proofBytes : List UInt8) (frontierNodes : Nat) where
  frontierCap : frontierNodes ≤ 203
  bodyLength : proofBytes.length = 19948 + 52 * frontierNodes
  packed : PackedFixedSection
  packedPrefix : ∀ index : Fin 9936,
    proofBytes[index.val]? =
      some (tagByteEquivExactByte.symm (packed index))
  exact : ExactCanonicalPackedFixedSection packed
  stored : FixedFieldView QM31Exact
  storedExact : StoredFixedFieldViewExact stored
    (decodedPackedFields packed exact.canonical)

/-- The exact decoded family selected by the successful translated reader
trace. -/
def ExactSourceFixedFieldTrace.decoded
    {proofBytes : List UInt8} {frontierNodes : Nat}
    (trace : ExactSourceFixedFieldTrace proofBytes frontierNodes) :
    DecodedFixedFields :=
  decodedPackedFields trace.packed trace.exact.canonical

/-- Final frozen-model conclusion for an arbitrary base tape.  The base tape
is data, not a correspondence premise: only its fixed prover-message fields
are replaced by the exact packed-section projection.  Search witnesses,
frontier counts, secure-circle returns, and all non-fixed message fields are
preserved by `tapeWithPackedFixedFields`.
-/
def ExactSourceFixedFieldConclusion
    (proofBytes : List UInt8) (frontierNodes : Nat)
    (tape : DeployedFixedTape) : Prop :=
  ∃ trace : ExactSourceFixedFieldTrace proofBytes frontierNodes,
    ∃ decoded : Fin 641 → QM31Exact,
      CurrentSourceFixedFieldProjection
          (rawOfMessages
            (tapeWithPackedFixedFields tape trace.packed).messages)
          decoded ∧
      FixedFieldDecodeExact
        (rawOfMessages
          (tapeWithPackedFixedFields tape trace.packed).messages)
        decoded ∧
      packedFixedFieldView trace.packed trace.exact.canonical =
        decodedFixedFieldView decoded ∧
      CanonicalFixedPadding (trace.packed ⟨9935, by norm_num⟩) ∧
      trace.stored =
        packedFixedFieldView trace.packed trace.exact.canonical

/-- Pure final composition.  The generated-source layer may invoke this only
after it has constructed `trace` from literal production success.
-/
theorem exactSourceFixedFieldTrace_constructs_capstone
    {proofBytes : List UInt8} {frontierNodes : Nat}
    (tape : DeployedFixedTape)
    (trace : ExactSourceFixedFieldTrace proofBytes frontierNodes) :
    ExactSourceFixedFieldConclusion proofBytes frontierNodes tape := by
  obtain ⟨decoded, decodeExact, viewExact, paddingExact⟩ :=
    exactCanonicalPackedSection_constructs_projected_decode_and_view
      tape trace.packed trace.exact
  refine ⟨trace, decoded,
    fixed_field_decode_implies_current_source_projection decodeExact,
    decodeExact, viewExact, paddingExact, ?_⟩
  calc
    trace.stored = decodedFixedFieldView trace.decoded :=
      storedFixedFieldViewExact_eq_decodedFixedFieldView trace.storedExact
    _ = packedFixedFieldView trace.packed trace.exact.canonical := by
      exact (storedFixedFieldViewExact_eq_decodedFixedFieldView
        (packedFixedFieldView_storedFixedFieldViewExact trace.packed
          trace.exact.canonical)).symm

/-- Companion form for a separately supplied tape.  Its only tape/source
premise is literal fixed-message byte identity; it does not assume
canonicality, decoding, a stored-view equality, or acceptance.
-/
theorem exactSourceFixedFieldTrace_constructs_supplied_tape
    {proofBytes : List UInt8} {frontierNodes : Nat}
    {tape : DeployedFixedTape}
    (trace : ExactSourceFixedFieldTrace proofBytes frontierNodes)
    (messages : PackedFixedMessagesMatch tape trace.packed) :
    ∃ decoded : Fin 641 → QM31Exact,
      CurrentSourceFixedFieldProjection (rawOfMessages tape.messages) decoded ∧
      FixedFieldDecodeExact (rawOfMessages tape.messages) decoded ∧
      packedFixedFieldView trace.packed trace.exact.canonical =
        decodedFixedFieldView decoded ∧
      CanonicalFixedPadding (trace.packed ⟨9935, by norm_num⟩) ∧
      trace.stored =
        packedFixedFieldView trace.packed trace.exact.canonical := by
  obtain ⟨decoded, decodeExact, viewExact, paddingExact⟩ :=
    packedFixedMessagesMatch_constructs_exact_decode_and_canonical_view
      messages trace.exact
  refine ⟨decoded,
    fixed_field_decode_implies_current_source_projection decodeExact,
    decodeExact, viewExact, paddingExact, ?_⟩
  calc
    trace.stored = decodedFixedFieldView trace.decoded :=
      storedFixedFieldViewExact_eq_decodedFixedFieldView trace.storedExact
    _ = packedFixedFieldView trace.packed trace.exact.canonical := by
      exact (storedFixedFieldViewExact_eq_decodedFixedFieldView
        (packedFixedFieldView_storedFixedFieldViewExact trace.packed
          trace.exact.canonical)).symm

/-!
## Pending literal generated-source theorem

Once `V7Tag73FixedFieldProduction/Funs.lean` exists, the source file importing
this interface must prove the following shape (with the exact emitted types):

```lean
theorem translated_caller_success_constructs_exact_fixed_fields
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (proof : Slice Std.U8) (frontierNodes : Std.Usize)
    (programId : solana_pubkey.Pubkey)
    (releaseBinding : Array Std.U8 32#usize)
    (attemptId : solana_pubkey.Pubkey)
    (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
    (statementDigest : Array Std.U8 32#usize) (checkPow : Bool)
    (output : v7_verifier.VerifiedV7ReadOnly)
    (run :
      v7_verifier.verify_v7_read_only_with_statement_digest
        hash proof frontierNodes programId releaseBinding attemptId statement
          statementDigest checkPow = .ok (.Ok output)) :
    ∀ tape : DeployedFixedTape,
      ExactSourceFixedFieldConclusion
        (generatedSliceBytes proof) frontierNodes.val tape := by
  -- Invert `run`; construct `ExactSourceFixedFieldTrace`; apply
  -- `exactSourceFixedFieldTrace_constructs_capstone`.
```

There is no theorem with a trace or agreement premise standing in for this
literal caller inversion.
-/

#print axioms exactSourceFixedFieldTrace_constructs_capstone
#print axioms exactSourceFixedFieldTrace_constructs_supplied_tape

end AspisV7Tag73FixedFieldSourceCapstone
