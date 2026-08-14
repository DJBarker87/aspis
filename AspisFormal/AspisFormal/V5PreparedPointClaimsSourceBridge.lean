import AspisFormal.V5ComponentCPreProjectionDeployed
import AspisFormal.V5ComponentCQM31Representation
import AspisFormal.V5ComponentCRelationTailCodec
import AspisFormal.V5ExactRuntimeWireRepair

/-!
# Production V5 prepared point-claim layout

This file isolates the field-independent part of
`prepare_v5_pcs_claims`: the exact 4-by-19 point-major byte layout, the
runtime caller slice, the gamma-power recurrence, and the five dot-product
blocks.  The companion Aeneas proof connects the production QM31 decoder and
the extracted power-building kernel to these definitions.
-/

namespace AspisV5PreparedPointClaimsSourceBridge

open AspisV5ComponentCPreProjectionDeployed
open AspisV5ComponentCQM31Representation
open AspisV5ComponentCRelationTailCodec
open AspisV5ComponentCRejectionSampler
open AspisFormal.V5ExactRuntimeWireRepair

abbrev SourceByte := Fin 256

abbrev SourcePointClaimBytes :=
  Fin (76 * qm31EncodedByteCount) → SourceByte

def sourcePointClaimByteIndexEquiv :
    (Fin 76 × Fin qm31EncodedByteCount) ≃
      Fin (76 * qm31EncodedByteCount) :=
  finProdFinEquiv

def sourcePointClaimFieldBytes (bytes : SourcePointClaimBytes)
    (field : Fin 76) : QM31Bytes :=
  fun byte => bytes (sourcePointClaimByteIndexEquiv (field, byte))

def decodeSourcePointClaimField (bytes : SourcePointClaimBytes)
    (field : Fin 76) : Option QM31Limbs :=
  decodeQM31LE (sourcePointClaimFieldBytes bytes field)

theorem source_point_claim_table_dimensions :
    4 * 19 = 76 ∧ 76 * qm31EncodedByteCount = 1216 := by
  decide

theorem source_point_claim_byte_index
    (point : PointClaimRow) (lane : TotalLane)
    (byte : Fin qm31EncodedByteCount) :
    (sourcePointClaimByteIndexEquiv
      (pointMajorClaimLayout (point, lane), byte)).val =
        16 * (19 * point.val + lane.val) + byte.val := by
  change byte.val + 16 * (lane.val + 19 * point.val) =
    16 * (19 * point.val + lane.val) + byte.val
  ring

theorem source_point_claim_field_byte_exact
    (bytes : SourcePointClaimBytes) (point : PointClaimRow)
    (lane : TotalLane) (byte : Fin qm31EncodedByteCount) :
    sourcePointClaimFieldBytes bytes
        (pointMajorClaimLayout (point, lane)) byte =
      bytes ⟨16 * (19 * point.val + lane.val) + byte.val, by
        have hpoint := point.isLt
        have hlane := lane.isLt
        have hbyte := byte.isLt
        norm_num [pointClaimRows, totalLaneCount,
          qm31EncodedByteCount] at hpoint hlane hbyte ⊢
        omega⟩ := by
  apply congrArg bytes
  apply Fin.ext
  exact source_point_claim_byte_index point lane byte

/-! ## Exact caller slice in the accepted mode-9 body -/

abbrev SourceRuntimeBodyBytes := Fin repairedFixedBytes → SourceByte

def sourceRuntimeClaimTable (body : SourceRuntimeBodyBytes) :
    SourcePointClaimBytes :=
  fun index => body ⟨relationClaimsOffset + index.val, by
    have hindex := index.isLt
    norm_num [relationClaimsOffset, repairedFixedBytes,
      qm31EncodedByteCount] at hindex ⊢
    omega⟩

theorem source_runtime_claim_span_exact :
    relationAlphasOffset - relationClaimsOffset = 1216 ∧
      relationClaimsOffset + 76 * qm31EncodedByteCount =
        relationAlphasOffset := by
  norm_num [relationClaimsOffset, relationAlphasOffset,
    qm31EncodedByteCount]

theorem source_runtime_point_claim_byte_exact
    (body : SourceRuntimeBodyBytes) (point : PointClaimRow)
    (lane : TotalLane) (byte : Fin qm31EncodedByteCount) :
    sourcePointClaimFieldBytes (sourceRuntimeClaimTable body)
        (pointMajorClaimLayout (point, lane)) byte =
      body ⟨relationClaimsOffset +
          16 * (19 * point.val + lane.val) + byte.val, by
        have hpoint := point.isLt
        have hlane := lane.isLt
        have hbyte := byte.isLt
        norm_num [relationClaimsOffset, repairedFixedBytes,
          pointClaimRows, totalLaneCount,
          qm31EncodedByteCount] at hpoint hlane hbyte ⊢
        omega⟩ := by
  rw [source_point_claim_field_byte_exact]
  apply congrArg body
  apply Fin.ext
  simp only [sourceRuntimeClaimTable]
  omega

/-! ## Gamma powers and five-block point claims -/

variable {K : Type*} [Field K]

def sourceGammaWeight (gamma : K) (lane : TotalLane) : K :=
  gamma ^ lane.val

/-- One source iteration after the fixed entries `1` and `gamma`.
Even exponents square the half exponent; odd exponents multiply the previous
power by gamma. -/
def sourceGammaPowerStep (gamma : K) (exponent : Nat) : K :=
  if exponent % 2 = 0 then
    (gamma ^ (exponent / 2)) ^ 2
  else
    gamma ^ (exponent - 1) * gamma

theorem source_gamma_power_step_exact (gamma : K) (exponent : Nat)
    (lower : 2 ≤ exponent) (upper : exponent < 19) :
    sourceGammaPowerStep gamma exponent = gamma ^ exponent := by
  interval_cases exponent <;>
    norm_num [sourceGammaPowerStep, pow_succ] <;> ring

theorem source_gamma_initial_powers (gamma : K) :
    sourceGammaWeight gamma ⟨0, by decide⟩ = 1 ∧
      sourceGammaWeight gamma ⟨1, by decide⟩ = gamma := by
  simp [sourceGammaWeight]

def sourcePointClaim (gamma : K) (claims : Fin 76 → K)
    (point : PointClaimRow) : K :=
  ∑ lane : TotalLane,
    sourceGammaWeight gamma lane *
      claims (pointMajorClaimLayout (point, lane))

/-- Production partitions columns as `4 + 4 + 4 + 4 + 3`. -/
def sourceClaimBlockOfLane (lane : TotalLane) : Fin 5 :=
  if h : lane.val < 16 then
    ⟨lane.val / 4, by omega⟩
  else
    ⟨4, by decide⟩

def sourcePointClaimBlock (gamma : K) (claims : Fin 76 → K)
    (point : PointClaimRow) (block : Fin 5) : K :=
  ∑ lane : TotalLane,
    if sourceClaimBlockOfLane lane = block then
      sourceGammaWeight gamma lane *
        claims (pointMajorClaimLayout (point, lane))
    else
      0

def sourcePreparedPointClaim (gamma : K) (claims : Fin 76 → K)
    (point : PointClaimRow) : K :=
  ∑ block : Fin 5, sourcePointClaimBlock gamma claims point block

def sourcePreparedPointClaims (gamma : K) (claims : Fin 76 → K) :
    PointClaimRow → K :=
  fun point => sourcePreparedPointClaim gamma claims point

theorem source_point_claim_block_sizes :
    (Finset.univ.filter
      (fun lane : TotalLane => sourceClaimBlockOfLane lane = (0 : Fin 5))).card = 4 ∧
    (Finset.univ.filter
      (fun lane : TotalLane => sourceClaimBlockOfLane lane = (1 : Fin 5))).card = 4 ∧
    (Finset.univ.filter
      (fun lane : TotalLane => sourceClaimBlockOfLane lane = (2 : Fin 5))).card = 4 ∧
    (Finset.univ.filter
      (fun lane : TotalLane => sourceClaimBlockOfLane lane = (3 : Fin 5))).card = 4 ∧
    (Finset.univ.filter
      (fun lane : TotalLane => sourceClaimBlockOfLane lane = (4 : Fin 5))).card = 3 := by
  decide

/-- The production block partition neither drops nor duplicates a lane. -/
theorem sourcePreparedPointClaim_eq_sourcePointClaim
    (gamma : K) (claims : Fin 76 → K) (point : PointClaimRow) :
    sourcePreparedPointClaim gamma claims point =
      sourcePointClaim gamma claims point := by
  classical
  unfold sourcePreparedPointClaim sourcePointClaimBlock sourcePointClaim
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro lane _
  simp

#print axioms source_point_claim_table_dimensions
#print axioms source_point_claim_byte_index
#print axioms source_point_claim_field_byte_exact
#print axioms source_runtime_claim_span_exact
#print axioms source_runtime_point_claim_byte_exact
#print axioms source_gamma_power_step_exact
#print axioms source_gamma_initial_powers
#print axioms source_point_claim_block_sizes
#print axioms sourcePreparedPointClaim_eq_sourcePointClaim

end AspisV5PreparedPointClaimsSourceBridge
