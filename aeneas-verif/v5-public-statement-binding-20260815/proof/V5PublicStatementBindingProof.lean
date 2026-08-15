import AspisV5TerminalExtract.Funs
import AspisFormal.V5AcceptedSpendRelation

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5PublicStatementBinding

open V5PublicStatementGenerated
open AspisFormal.ArithmetizationCore
open AspisV5AcceptedSpendRelation

abbrev RustStatement :=
  aspis_statement.atomic_statement.AtomicPaymentStatementV4

def arrayAt8 (array : Array Std.U32 8#usize) (index : Fin 8) : Std.U32 :=
  array.val.get ⟨index.val, by
    rw [array.property]
    simpa using index.isLt⟩

def rustDigest (array : Array Std.U32 8#usize) : Digest :=
  fun index => (arrayAt8 array index).val

structure SixSpendFields where
  currentAnchor : Digest
  nullifier : Digest
  outputCommitment : Digest
  outputAnchor : Digest
  asset : F
  fee : Nat

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

structure OpenedColumnsMatchRustStatement
    (statement : RustStatement) (opened : OpenedColumns) : Prop where
  currentAnchor : opened.A = (rustSpendFields statement).currentAnchor
  nullifier : opened.nu = (rustSpendFields statement).nullifier
  outputCommitment :
    opened.C_out = (rustSpendFields statement).outputCommitment
  outputAnchor : opened.A' = (rustSpendFields statement).outputAnchor
  asset : opened.a = (rustSpendFields statement).asset
  fee : opened.f = (rustSpendFields statement).fee

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
      (congrArg SixSpendFields.currentAnchor fields)
  · exact openedMatchesDecoded.nullifier.trans
      (congrArg SixSpendFields.nullifier fields)
  · exact openedMatchesDecoded.outputCommitment.trans
      (congrArg SixSpendFields.outputCommitment fields)
  · exact openedMatchesDecoded.outputAnchor.trans
      (congrArg SixSpendFields.outputAnchor fields)
  · exact openedMatchesDecoded.asset.trans
      (congrArg SixSpendFields.asset fields)
  · exact openedMatchesDecoded.fee.trans
      (congrArg SixSpendFields.fee fields)

/-! The only mathematical statement-binding premise left after the source
decoder and live-equality check is the PCS/extraction fact that the accepted
opening table has these six terminal values. -/
def RemainingPCSStatementBinding
    (decoded : RustStatement) (opened : OpenedColumns) : Prop :=
  OpenedColumnsMatchRustStatement decoded opened

#print axioms decode_statement_success_unique
#print axioms decode_statement_success_binds_unique_six_fields
#print axioms decoded_context_equal_live_binds_all_six_fields
#print axioms opened_columns_match_maintained_statement

end AspisV5PublicStatementBinding
