import V5FriDecoderProof
import AspisFormal.V5PreparedPointClaimsSourceBridge

/-!
# Extracted V5 point-claim decoder bridge

This file connects the production QM31 byte decoder extracted by Charon and
Aeneas to the exact 76-field point-major claim-table model.  It is separate
from the prepared-claim arithmetic proof because the two source-authentic
extraction packages intentionally use different generated namespaces.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5PreparedPointClaimsSourceProof

open AspisV5ComponentCQM31Representation
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCPreProjectionDeployed
open AspisV5PreparedPointClaimsSourceBridge

/-- Apply the extracted production QM31 decoder to one of the 76 exact
sixteen-byte source fields. -/
def extractedPointClaimField (bytes : SourcePointClaimBytes)
    (field : Fin 76) : Option QM31Limbs :=
  AspisV5FriDecoderSourceProof.extractedQM31Decode
    (sourcePointClaimFieldBytes bytes field)

/-- Every one of the 76 extracted field decodes equals the maintained
little-endian model, for every possible 1,216-byte table. -/
theorem extracted_point_claim_field_eq_model
    (bytes : SourcePointClaimBytes) (field : Fin 76) :
    extractedPointClaimField bytes field =
      decodeSourcePointClaimField bytes field := by
  exact AspisV5FriDecoderSourceProof.extractedQM31Decode_eq_model _

/-- Assemble a whole table from an arbitrary single-field decoder.  This
definition records the same all-fields-success condition independently of
the order in which a concrete loop checks the fields. -/
noncomputable def decodePointClaimTableWith
    (decode : QM31Bytes → Option QM31Limbs)
    (bytes : SourcePointClaimBytes) : Option (Fin 76 → QM31Limbs) := by
  classical
  exact if h : ∀ field, ∃ value,
      decode (sourcePointClaimFieldBytes bytes field) = some value then
    some (fun field => Classical.choose (h field))
  else
    none

theorem decodePointClaimTableWith_congr
    (left right : QM31Bytes → Option QM31Limbs)
    (equal : left = right) :
    decodePointClaimTableWith left = decodePointClaimTableWith right := by
  subst right
  rfl

/-- Universal equality of the fieldwise 76-entry table decoder assembled
from extracted production calls and the maintained mathematical decoder. -/
theorem extracted_point_claim_table_eq_model :
    decodePointClaimTableWith
        AspisV5FriDecoderSourceProof.extractedQM31Decode =
      decodePointClaimTableWith decodeQM31LE := by
  apply decodePointClaimTableWith_congr
  funext bytes
  exact AspisV5FriDecoderSourceProof.extractedQM31Decode_eq_model bytes

/-- The exact runtime caller slice inherits the same per-field equality. -/
theorem extracted_runtime_point_claim_field_eq_model
    (body : SourceRuntimeBodyBytes) (point : PointClaimRow)
    (lane : TotalLane) :
    extractedPointClaimField (sourceRuntimeClaimTable body)
        (pointMajorClaimLayout (point, lane)) =
      decodeSourcePointClaimField (sourceRuntimeClaimTable body)
        (pointMajorClaimLayout (point, lane)) := by
  exact extracted_point_claim_field_eq_model _ _

#print axioms extracted_point_claim_field_eq_model
#print axioms decodePointClaimTableWith_congr
#print axioms extracted_point_claim_table_eq_model
#print axioms extracted_runtime_point_claim_field_eq_model

end AspisV5PreparedPointClaimsSourceProof
