import AspisFormal.K1.V7Tag73DerivedK13View
import AspisFormal.K1.V7Tag73ExactFixedInstanceEvent
import AspisFormal.K1.V7Tag73SemanticTranscriptBridge

/-!
# Current-source fixed-field and parsed-view boundary

The current Rust verifier reads the packed 641-QM31 fixed-field section with
`V6FixedFieldReader`, consumes all 641 values, and calls `finish` before it can
return a verified transcript.  The operational source certificate used by the
K1 compiler does not yet expose that reader result: `checkedRefine` checks the
verifier-derived challenge and q16 decoders, but deliberately treats prover
field bytes as transcript payloads.

This file gives the smallest byte/value projection that a current-revision
source extraction must produce and proves that it is exactly equivalent to
`FixedFieldDecodeExact`.  It then transports the result through the existing
fixed-clean-root raw-message equality.

The production wire parser also does not return verifier challenges, q16, or
a total inverse table.  The correct K1.3 object is therefore the already
defined `derivedK13View`: openings come from the parsed wire, fixed fields from
the source reader, and verifier-derived values from the operational run.  The
last section isolates the single equality needed while consumers still use
the older opaque `rawProof` projection.  No source/Aeneas theorem establishing
that equality is asserted here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73CurrentSourceDecodeBridge

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73DerivedK13View
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73SemanticTranscriptBridge
open AspisK1.V7Tag73SecureCircleMap
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-! ## Exact current-source fixed-field projection -/

/-- Byte/value output expected from the current source reader.  This is a
coordinatewise representation equality, not an acceptance, probability, or
soundness conclusion. -/
def CurrentSourceFixedFieldProjection
    (raw : RawTag73ProverMessages) (decoded : Fin 641 → QM31Exact) : Prop :=
  ∀ index,
    rawFixedFieldBytes raw index = encodeTagQM31ExactLE (decoded index)

/-- The source-shaped byte projection implies the exact decoder interface
used by K1.3--K1.5. -/
theorem current_source_fixed_field_projection_implies_decode
    {raw : RawTag73ProverMessages} {decoded : Fin 641 → QM31Exact}
    (source : CurrentSourceFixedFieldProjection raw decoded) :
    FixedFieldDecodeExact raw decoded := by
  intro index
  rw [source index]
  exact decodeTagQM31ExactLE_encodeTagQM31ExactLE _

/-- Conversely, successful exact decoding recovers the literal canonical
bytes.  Thus the source obligation above is neither stronger nor weaker than
the required fixed-field decoder fact. -/
theorem fixed_field_decode_implies_current_source_projection
    {raw : RawTag73ProverMessages} {decoded : Fin 641 → QM31Exact}
    (decodedExact : FixedFieldDecodeExact raw decoded) :
    CurrentSourceFixedFieldProjection raw decoded := by
  intro index
  exact (encodeTagQM31ExactLE_of_decode
    (rawFixedFieldBytes raw index) (decoded index)
    (decodedExact index)).symm

theorem current_source_fixed_field_projection_iff_decode
    (raw : RawTag73ProverMessages) (decoded : Fin 641 → QM31Exact) :
    CurrentSourceFixedFieldProjection raw decoded ↔
      FixedFieldDecodeExact raw decoded := by
  exact ⟨current_source_fixed_field_projection_implies_decode,
    fixed_field_decode_implies_current_source_projection⟩

/-- Transport a current-source reader result through the literal raw-message
equality already contained in a fixed clean root. -/
theorem fixed_clean_root_has_exact_fixed_field_decode_of_current_source
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (fixed : ExactFixedCleanSourceRootProjection transitionFuel configuration
      projection fixedInstance sample)
    (source : ∃ decoded : Fin 641 → QM31Exact,
      CurrentSourceFixedFieldProjection
        fixed.base.runtime.adversaryValue.rawMessages decoded) :
    ∃ decoded : Fin 641 → QM31Exact,
      FixedFieldDecodeExact (fixedTapeRawMessages fixed.base.tape) decoded := by
  rcases source with ⟨decoded, source⟩
  refine ⟨decoded, ?_⟩
  rw [fixed.base.rawMessagesExact]
  exact current_source_fixed_field_projection_implies_decode source

/-! ## Correct parsed-wire projection -/

/-- While the old classifier still reads an opaque `rawProof`, the exact
source/model migration obligation is equality with the derived view.  This is
one data equality: it says that parser-owned openings are retained while the
other fields are projections of the operational transcript and fixed-field
reader. -/
def ExactOperationalParsedWireProjection
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (decoded : Fin 641 → QM31Exact) : Prop :=
  exactK13ParsedProof input =
    derivedK13View input decoded (exactK13ParsedProof input).openings

/-- The exact parsed-wire projection constructs the legacy binding record.
The inverse-table field is discharged by the canonical schedule theorem, not
by a source assumption. -/
theorem exact_parsed_proof_source_binding_of_operational_projection
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (decoded : Fin 641 → QM31Exact)
    (source : ExactOperationalParsedWireProjection input decoded) :
    ExactParsedProofSourceBinding input decoded := by
  unfold ExactOperationalParsedWireProjection at source
  refine
    { gammaExact := ?_
      alphaZeroExact := ?_
      disclosedFinalExact := ?_
      selectedQueriesExact := ?_
      inverseTablesExact := ?_ }
  · rw [source]
    exact derived_k13_view_gamma input decoded _
  · rw [source]
    exact derived_k13_view_alpha_zero input decoded _
  · rw [source]
    exact derived_k13_view_disclosed_final input decoded _
  · rw [source]
    exact derived_k13_view_queries input decoded _
  · rw [source]
    exact derived_k13_view_inverse_tables input decoded _

/-- Fixed-field source projection and parsed-wire projection compose without
any new semantic or probability premise. -/
theorem current_source_outputs_construct_decode_and_parsed_binding
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (decoded : Fin 641 → QM31Exact)
    (fixedFields : CurrentSourceFixedFieldProjection
      (fixedTapeRawMessages (exactOperationalTape input)) decoded)
    (parsed : ExactOperationalParsedWireProjection input decoded) :
    FixedFieldDecodeExact
        (fixedTapeRawMessages (exactOperationalTape input)) decoded ∧
      ExactParsedProofSourceBinding input decoded := by
  exact ⟨current_source_fixed_field_projection_implies_decode fixedFields,
    exact_parsed_proof_source_binding_of_operational_projection input decoded
      parsed⟩

#print axioms current_source_fixed_field_projection_implies_decode
#print axioms fixed_field_decode_implies_current_source_projection
#print axioms current_source_fixed_field_projection_iff_decode
#print axioms fixed_clean_root_has_exact_fixed_field_decode_of_current_source
#print axioms exact_parsed_proof_source_binding_of_operational_projection
#print axioms current_source_outputs_construct_decode_and_parsed_binding

end

end AspisK1.V7Tag73CurrentSourceDecodeBridge
