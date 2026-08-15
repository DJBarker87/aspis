import AspisV5TerminalExtract.Funs
import AspisFormal.V5AcceptedSpendRelation
import AspisFormal.V5ProductionPublicResidualBinding

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5PublicStatementBinding

open V5PublicStatementGenerated
open AspisFormal.ArithmetizationCore
open AspisV5AcceptedSpendRelation
open AspisV5ProductionPublicResidualBinding

abbrev RustStatement :=
  aspis_statement.atomic_statement.AtomicPaymentStatementV4

def arrayAt8 (array : Array Std.U32 8#usize) (index : Fin 8) : Std.U32 :=
  array.val.get ⟨index.val, by
    rw [array.property]
    simpa using index.isLt⟩

def rustDigest (array : Array Std.U32 8#usize) : Digest :=
  fun index => (arrayAt8 array index).val

abbrev SixSpendFields := TerminalSpendFields

def rustSpendFields (statement : RustStatement) : SixSpendFields where
  currentAnchor := rustDigest statement.spend.anchor
  nullifier := rustDigest statement.spend.nullifier
  outputCommitment := rustDigest statement.spend.output_commitment
  outputAnchor := rustDigest statement.output_anchor
  asset := statement.spend.asset_id.val
  fee := statement.spend.fee.val

def maintainedSpendFields (statement : V5PublicStatement) : SixSpendFields where
  currentAnchor := statement.currentAnchor
  nullifier := statement.nullifier
  outputCommitment := statement.outputCommitment
  outputAnchor := statement.outputAnchor
  asset := statement.asset
  fee := statement.fee

/-! A deterministic source-extracted decoder cannot return two different
statements for the same payload.  This theorem is deliberately independent of
any test vector or released byte string. -/
theorem decode_statement_success_unique
    (bytes : Slice Std.U8) (left right : RustStatement)
    (hleft : v5_atomic_terminal.decode_statement bytes = .ok (.Ok left))
    (hright : v5_atomic_terminal.decode_statement bytes = .ok (.Ok right)) :
    left = right := by
  rw [hleft] at hright
  simpa using hright

theorem decode_statement_success_binds_unique_six_fields
    (bytes : Slice Std.U8) (left right : RustStatement)
    (hleft : v5_atomic_terminal.decode_statement bytes = .ok (.Ok left))
    (hright : v5_atomic_terminal.decode_statement bytes = .ok (.Ok right)) :
    rustSpendFields left = rustSpendFields right := by
  rw [decode_statement_success_unique bytes left right hleft hright]

/-! This is the exact consequence of the production wire-prefix equality
check `context_statement == live_statement`: all six relation fields, not only
the statement digest, are identical. -/
theorem decoded_context_equal_live_binds_all_six_fields
    (decoded live : RustStatement) (hequal : decoded = live) :
    rustSpendFields decoded = rustSpendFields live := by
  subst live
  rfl

abbrev OpenedColumnsMatchRustStatement
    (statement : RustStatement) (opened : OpenedColumns) :=
  OpenedColumnsMatchTerminalSpendFields (rustSpendFields statement) opened

/-! Once the authenticated polynomial openings are tied to the terminal's
six values, equality of the decoded terminal statement and the live statement
is enough to construct the maintained public-field predicate.  No additional
public-field assumption is hidden in this composition. -/
theorem opened_columns_match_maintained_statement
    (decoded live : RustStatement)
    (statement : V5PublicStatement) (opened : OpenedColumns)
    (decodedIsLive : decoded = live)
    (liveRepresentsStatement :
      rustSpendFields live = maintainedSpendFields statement)
    (openedMatchesDecoded : OpenedColumnsMatchRustStatement decoded opened) :
    OpenedColumnsMatchStatement statement opened := by
  have fields : rustSpendFields decoded = maintainedSpendFields statement :=
    (decoded_context_equal_live_binds_all_six_fields decoded live
      decodedIsLive).trans liveRepresentsStatement
  constructor
  · exact openedMatchesDecoded.currentAnchor.trans
      (congrArg TerminalSpendFields.currentAnchor fields)
  · exact openedMatchesDecoded.nullifier.trans
      (congrArg TerminalSpendFields.nullifier fields)
  · exact openedMatchesDecoded.outputCommitment.trans
      (congrArg TerminalSpendFields.outputCommitment fields)
  · exact openedMatchesDecoded.outputAnchor.trans
      (congrArg TerminalSpendFields.outputAnchor fields)
  · exact openedMatchesDecoded.asset.trans
      (congrArg TerminalSpendFields.asset fields)
  · exact openedMatchesDecoded.fee.trans
      (congrArg TerminalSpendFields.fee fields)

/-! The remaining PCS/sumcheck step is now stated as the exact raw residual
condition used by the production terminal, rather than assuming the desired
six field equalities directly. -/
def RemainingPCSStatementBinding
    (decoded : RustStatement) (opened : OpenedColumns)
    (z : Fin 1024 → Fin 16 → F) : Prop :=
  ExtractedProductionTracePublicResiduals (rustSpendFields decoded) opened z

/-- The exact residual premise, the maintained arithmetic constraints, and
the source-extracted live-statement equality imply all six public field
equalities.  This holds for every successful statement and opening record; it
does not rely on the released proof bytes. -/
theorem production_public_residuals_bind_live_statement
    (decoded live : RustStatement)
    (statement : V5PublicStatement) (opened : OpenedColumns)
    (decodedIsLive : decoded = live)
    (liveRepresentsStatement :
      rustSpendFields live = maintainedSpendFields statement)
    (constraints : ConstraintsSatisfied opened)
    (z : Fin 1024 → Fin 16 → F)
    (residuals : RemainingPCSStatementBinding decoded opened z) :
    OpenedColumnsMatchStatement statement opened := by
  have fields :
      rustSpendFields decoded = terminalSpendFields statement := by
    exact (decoded_context_equal_live_binds_all_six_fields decoded live
      decodedIsLive).trans liveRepresentsStatement
  change ExtractedProductionTracePublicResiduals
    (rustSpendFields decoded) opened z at residuals
  rw [fields] at residuals
  exact extracted_production_trace_binds_statement statement opened constraints
    z residuals

/-- Equivalently, outside the one explicitly named residual-extraction
failure, the production terminal binds all six fields.  No cryptographic
probability is assigned to that failure here. -/
def PublicResidualExtractionFailure
    (decoded : RustStatement) (opened : OpenedColumns)
    (z : Fin 1024 → Fin 16 → F) : Prop :=
  ¬ RemainingPCSStatementBinding decoded opened z

theorem no_public_residual_extraction_failure_binds_live_statement
    (decoded live : RustStatement)
    (statement : V5PublicStatement) (opened : OpenedColumns)
    (decodedIsLive : decoded = live)
    (liveRepresentsStatement :
      rustSpendFields live = maintainedSpendFields statement)
    (constraints : ConstraintsSatisfied opened)
    (z : Fin 1024 → Fin 16 → F)
    (outsideFailure :
      ¬ PublicResidualExtractionFailure decoded opened z) :
    OpenedColumnsMatchStatement statement opened := by
  apply production_public_residuals_bind_live_statement decoded live statement
    opened decodedIsLive liveRepresentsStatement constraints z
  exact Classical.byContradiction outsideFailure

/-! ## Exact terminal claim-table layout

The production terminal reads a point-major `4 × 19` table.  The first
three points and lanes `0..15` are copied into the old semantic slots; lane 16
is copied into old column 26.  Old columns `16..25` and 27 remain zero.  The
mask is the fourth point's lane 17.  These definitions spell out that direct
indexing without making a polynomial-commitment claim. -/

def extractedClaimBody
    (bytes : Slice Std.U8) (point lane : Std.Usize) :
    Result (core.result.Result aspis_core.field.QM31
      v5_atomic_terminal.V5AtomicTerminalError) := do
  let i ← point * 19#usize
  let value ← i + lane
  let start ← value * 16#usize
  let stop ← start + 16#usize
  let slice ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
    bytes { start, «end» := stop }
  let value ← aspis_core.field.QM31.from_le_bytes slice
  core.option.Option.ok_or value
    (v5_atomic_terminal.V5AtomicTerminalError.NonCanonicalClaim point lane)

/-- The Aeneas translation of the production `claim` helper uses exactly
`16 * (19 * point + lane)` as the start of the field encoding. -/
theorem extracted_claim_uses_exact_point_major_offset
    (bytes : Slice Std.U8) (point lane : Std.Usize) :
    v5_atomic_terminal.claim bytes point lane =
      extractedClaimBody bytes point lane := by
  simp only [v5_atomic_terminal.claim, extractedClaimBody,
    v5_atomic_terminal.V5_ATOMIC_TERMINAL_LANES]

def pointMajorIndex (point lane : Nat) : Nat := point * 19 + lane

def pointMajorByteStart (point lane : Nat) : Nat :=
  16 * pointMajorIndex point lane

def terminalLegacyAdapter {T : Type} [OfNat T 0]
    (claims : Nat → Nat → T) (point column : Nat) : T :=
  if column < 16 then claims point column
  else if column = 26 then claims point 16
  else 0

theorem terminal_adapter_copies_each_semantic_lane
    {T : Type} [OfNat T 0] (claims : Nat → Nat → T)
    (point lane : Nat) (laneBound : lane < 16) :
    terminalLegacyAdapter claims point lane = claims point lane := by
  simp [terminalLegacyAdapter, laneBound]

theorem terminal_adapter_copies_hcopy
    {T : Type} [OfNat T 0] (claims : Nat → Nat → T)
    (point : Nat) :
    terminalLegacyAdapter claims point 26 = claims point 16 := by
  simp [terminalLegacyAdapter]

theorem terminal_adapter_zeros_removed_columns
    {T : Type} [OfNat T 0] (claims : Nat → Nat → T)
    (point column : Nat) (lower : 16 ≤ column) (notHcopy : column ≠ 26) :
    terminalLegacyAdapter claims point column = 0 := by
  simp [terminalLegacyAdapter, Nat.not_lt.mpr lower, notHcopy]

theorem terminal_adapter_zeros_old_mask_and_g_slots
    {T : Type} [OfNat T 0] (claims : Nat → Nat → T)
    (point : Nat) :
    (∀ column, 16 ≤ column → column < 26 →
      terminalLegacyAdapter claims point column = 0) ∧
      terminalLegacyAdapter claims point 27 = 0 := by
  constructor
  · intro column lower upper
    exact terminal_adapter_zeros_removed_columns claims point column lower (by omega)
  · exact terminal_adapter_zeros_removed_columns claims point 27 (by omega) (by omega)

theorem terminal_mask_uses_fourth_point_lane_seventeen :
    pointMajorIndex 3 17 = 74 ∧
      pointMajorByteStart 3 17 = 1184 ∧
      pointMajorByteStart 3 17 + 16 = 1200 := by
  norm_num [pointMajorIndex, pointMajorByteStart]

theorem complete_claim_table_ends_at_1216_bytes :
    pointMajorByteStart 3 18 + 16 = 1216 := by
  norm_num [pointMajorIndex, pointMajorByteStart]

#print axioms decode_statement_success_unique
#print axioms decode_statement_success_binds_unique_six_fields
#print axioms decoded_context_equal_live_binds_all_six_fields
#print axioms opened_columns_match_maintained_statement
#print axioms production_public_residuals_bind_live_statement
#print axioms no_public_residual_extraction_failure_binds_live_statement
#print axioms extracted_claim_uses_exact_point_major_offset
#print axioms terminal_adapter_copies_each_semantic_lane
#print axioms terminal_adapter_copies_hcopy
#print axioms terminal_adapter_zeros_removed_columns
#print axioms terminal_adapter_zeros_old_mask_and_g_slots
#print axioms terminal_mask_uses_fourth_point_lane_seventeen
#print axioms complete_claim_table_ends_at_1216_bytes

end AspisV5PublicStatementBinding
