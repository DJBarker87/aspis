import AspisFormal.V5AcceptedSpendRelation

/-!
# Public values enforced by the production V5 terminal

This file models the public residuals that the production semantic evaluator
builds in `atomic_semantic_packed_impl`:

* the fee balance at row 864 and semantic position 66;
* four eight-limb digest equalities at rows 379, 699, 731, and 779 and
  semantic positions 67 through 74; and
* the input/output asset equalities at rows 795 and 799 and semantic
  positions 75 and 76.

The Rust evaluator multiplies these row residuals by multilinear equality
selectors, packs four adjacent semantic positions together, and then folds the
packed lanes with `theta`.  Later code multiplies the whole composition by the
zerocheck equality value and adds the helper term.  Therefore one accepted
terminal scalar does not, by itself, say that every residual below is zero.
The PCS/FRI and sumcheck extraction argument must establish that fact, or count
its failure as a soundness event.

What is proved here is the deterministic step after extraction: if these exact
production row residuals vanish, the opened relation uses the live anchor,
nullifier, output commitment, output anchor, asset, and fee.  The fee needs a
small extra argument because it is not a separate opening: Rust inserts the
live fee directly into the balance residual.  Comparing that residual with the
maintained balance equation, using both 30-bit bounds, proves equality of the
two natural-number fees.
-/

namespace AspisV5ProductionPublicResidualBinding

open AspisFormal.ArithmetizationCore
open AspisV5AcceptedSpendRelation

/-- The six values from the live Rust statement that occur in the semantic
terminal.  Pool, sequence, and deployment domain are transcript-bound but do
not occur in these relation residuals. -/
structure TerminalSpendFields where
  currentAnchor : Digest
  nullifier : Digest
  outputCommitment : Digest
  outputAnchor : Digest
  asset : F
  fee : Nat

/-- Projection of the maintained public statement to the six terminal fields. -/
def terminalSpendFields (statement : V5PublicStatement) : TerminalSpendFields where
  currentAnchor := statement.currentAnchor
  nullifier := statement.nullifier
  outputCommitment := statement.outputCommitment
  outputAnchor := statement.outputAnchor
  asset := statement.asset
  fee := statement.fee

/-- Digest order used by the production loop in `atomic_semantic_packed_impl`. -/
def terminalDigestField (fields : TerminalSpendFields) : Fin 4 → Digest
  | 0 => fields.currentAnchor
  | 1 => fields.outputAnchor
  | 2 => fields.nullifier
  | 3 => fields.outputCommitment

/-- Opened-column order corresponding to `terminalDigestField`. -/
def openedDigestField (opened : OpenedColumns) : Fin 4 → Digest
  | 0 => opened.A
  | 1 => opened.A'
  | 2 => opened.nu
  | 3 => opened.C_out

def openedAssetField (opened : OpenedColumns) : Fin 2 → F
  | 0 => opened.a_in
  | 1 => opened.a

/-- The exact rows selected by the four iterations of the production digest
loop: `(block * 16 + 11)` for blocks 23, 43, 45, and 48. -/
def terminalDigestRow : Fin 4 → Nat
  | 0 => 23 * 16 + 11
  | 1 => 43 * 16 + 11
  | 2 => 45 * 16 + 11
  | 3 => 48 * 16 + 11

theorem terminal_digest_rows_are_exact :
    terminalDigestRow 0 = 379 ∧
      terminalDigestRow 1 = 699 ∧
      terminalDigestRow 2 = 731 ∧
      terminalDigestRow 3 = 779 := by
  norm_num [terminalDigestRow]

/-- Coordinates of the raw public row residuals before selector
multiplication, four-at-a-time packing, and the `theta` fold. -/
inductive PublicResidualCoordinate where
  | feeBalance
  | digest (which : Fin 4) (limb : Fin 8)
  | asset (which : Fin 2)
  deriving DecidableEq, Fintype

/-- Exact production row selected for each raw residual. -/
def publicResidualRow : PublicResidualCoordinate → Nat
  | .feeBalance => 864
  | .digest which _ => terminalDigestRow which
  | .asset 0 => 795
  | .asset 1 => 799

/-- Exact semantic position before four-at-a-time packing.  The four digest
rows share positions 67 through 74 and are separated by their row selectors. -/
def publicResidualSemanticPosition : PublicResidualCoordinate → Nat
  | .feeBalance => 66
  | .digest _ limb => 67 + limb.val
  | .asset which => 75 + which.val

theorem public_residual_coordinate_count :
    Fintype.card PublicResidualCoordinate = 35 := by
  decide

theorem terminal_asset_rows_are_exact :
    publicResidualRow (.asset 0) = 795 ∧
      publicResidualRow (.asset 1) = 799 := by
  decide

theorem terminal_public_semantic_positions_are_exact :
    publicResidualSemanticPosition .feeBalance = 66 ∧
      (∀ which limb,
        publicResidualSemanticPosition (.digest which limb) = 67 + limb.val) ∧
      (∀ which,
        publicResidualSemanticPosition (.asset which) = 75 + which.val) := by
  decide

/-- The public cells read from one extracted production trace.  `inputValue`
and `outputValue` are columns 11 and 12 at row 864.  The other coordinates
come from the rows recorded by `publicResidualRow`. -/
structure ProductionPublicRowValues where
  inputValue : F
  outputValue : F
  digest : Fin 4 → Digest
  asset : Fin 2 → F

/-- Literal projection from a 1,024-by-16 production trace table to the cells
used by the public residuals. -/
def productionPublicRowsFromTrace
    (z : Fin 1024 → Fin 16 → F) : ProductionPublicRowValues where
  inputValue := z ⟨864, by omega⟩ ⟨11, by omega⟩
  outputValue := z ⟨864, by omega⟩ ⟨12, by omega⟩
  digest := fun which limb =>
    z ⟨terminalDigestRow which, by fin_cases which <;> decide⟩
      ⟨limb.val, by omega⟩
  asset
    | 0 => z ⟨795, by omega⟩ ⟨1, by omega⟩
    | 1 => z ⟨799, by omega⟩ ⟨1, by omega⟩

/-- Exact normalized-trace projection.  This keeps the Rust-row-to-model step
visible instead of silently identifying an arbitrary `OpenedColumns` value
with a production cell. -/
structure ProductionPublicRowsProjectToOpenedColumns
    (rows : ProductionPublicRowValues) (opened : OpenedColumns) : Prop where
  inputValue : rows.inputValue = opened.rin.value
  outputValue : rows.outputValue = opened.rout.value
  digest : ∀ which, rows.digest which = openedDigestField opened which
  asset : ∀ which, rows.asset which = openedAssetField opened which

/-- Raw source-row residual before projection into `OpenedColumns`. -/
def rowPublicResidual
    (fields : TerminalSpendFields) (rows : ProductionPublicRowValues) :
    PublicResidualCoordinate → F
  | .feeBalance => rows.inputValue - rows.outputValue - (fields.fee : F)
  | .digest which limb =>
      rows.digest which limb - terminalDigestField fields which limb
  | .asset which => rows.asset which - fields.asset

def ProductionPublicRowResidualsVanish
    (fields : TerminalSpendFields) (rows : ProductionPublicRowValues) : Prop :=
  ∀ coordinate, rowPublicResidual fields rows coordinate = 0

/-- Source-shaped public row residual.  Asset zero is the input asset and
asset one is the output asset. -/
def publicResidual
    (fields : TerminalSpendFields) (opened : OpenedColumns) :
    PublicResidualCoordinate → F
  | .feeBalance =>
      opened.rin.value - opened.rout.value - (fields.fee : F)
  | .digest which limb =>
      openedDigestField opened which limb - terminalDigestField fields which limb
  | .asset which => openedAssetField opened which - fields.asset

/-- Every raw public residual built by the production semantic evaluator
vanishes.  This is the precise deterministic output needed from the preceding
sumcheck/PCS extraction argument. -/
def ProductionPublicResidualsVanish
    (fields : TerminalSpendFields) (opened : OpenedColumns) : Prop :=
  ∀ coordinate, publicResidual fields opened coordinate = 0

/-- The precise deterministic evidence expected from trace extraction: fixed
production row values, their mapping to the maintained model, and vanishing
of all 35 public residuals. -/
structure ExtractedProductionPublicResiduals
    (fields : TerminalSpendFields) (opened : OpenedColumns)
    (rows : ProductionPublicRowValues) : Prop where
  projects : ProductionPublicRowsProjectToOpenedColumns rows opened
  vanish : ProductionPublicRowResidualsVanish fields rows

/-- Fixed-trace form.  A deployed reduction must supply the trace table
extracted from the accepted commitments; the deterministic theorem does not
choose a convenient table after seeing the statement. -/
def ExtractedProductionTracePublicResiduals
    (fields : TerminalSpendFields) (opened : OpenedColumns)
    (z : Fin 1024 → Fin 16 → F) : Prop :=
  ExtractedProductionPublicResiduals fields opened
    (productionPublicRowsFromTrace z)

theorem projected_row_residual_eq
    (fields : TerminalSpendFields) (opened : OpenedColumns)
    (rows : ProductionPublicRowValues)
    (projects : ProductionPublicRowsProjectToOpenedColumns rows opened)
    (coordinate : PublicResidualCoordinate) :
    rowPublicResidual fields rows coordinate =
      publicResidual fields opened coordinate := by
  cases coordinate with
  | feeBalance =>
      simp only [rowPublicResidual, publicResidual, projects.inputValue,
        projects.outputValue]
  | digest which limb =>
      simp only [rowPublicResidual, publicResidual]
      rw [projects.digest which]
  | asset which =>
      simp only [rowPublicResidual, publicResidual]
      rw [projects.asset which]

theorem normalized_residuals_of_extracted_rows
    (fields : TerminalSpendFields) (opened : OpenedColumns)
    (rows : ProductionPublicRowValues)
    (extracted : ExtractedProductionPublicResiduals fields opened rows) :
    ProductionPublicResidualsVanish fields opened := by
  intro coordinate
  rw [← projected_row_residual_eq fields opened rows
    extracted.projects coordinate]
  exact extracted.vanish coordinate

/-- Exact residual failure left to the sumcheck/PCS argument.  No probability
is assigned here. -/
def PublicResidualExtractionFailure
    (fields : TerminalSpendFields) (opened : OpenedColumns) : Prop :=
  ¬ ProductionPublicResidualsVanish fields opened

/-- Failure of the stronger row-explicit extraction statement. -/
def ExactPublicResidualExtractionFailure
    (fields : TerminalSpendFields) (opened : OpenedColumns)
    (z : Fin 1024 → Fin 16 → F) : Prop :=
  ¬ ExtractedProductionTracePublicResiduals fields opened z

/-- Direct six-field equality for a source-shaped terminal value record. -/
structure OpenedColumnsMatchTerminalSpendFields
    (fields : TerminalSpendFields) (opened : OpenedColumns) : Prop where
  currentAnchor : opened.A = fields.currentAnchor
  nullifier : opened.nu = fields.nullifier
  outputCommitment : opened.C_out = fields.outputCommitment
  outputAnchor : opened.A' = fields.outputAnchor
  asset : opened.a = fields.asset
  fee : opened.f = fields.fee

/-- Vanishing digest residuals recover each of the four public digests. -/
theorem digest_eq_of_public_residuals
    (fields : TerminalSpendFields) (opened : OpenedColumns)
    (residuals : ProductionPublicResidualsVanish fields opened)
    (which : Fin 4) :
    openedDigestField opened which = terminalDigestField fields which := by
  funext limb
  exact sub_eq_zero.mp (residuals (.digest which limb))

/-- Vanishing output-asset residual recovers the public asset. -/
theorem output_asset_eq_of_public_residuals
    (fields : TerminalSpendFields) (opened : OpenedColumns)
    (residuals : ProductionPublicResidualsVanish fields opened) :
    opened.a = fields.asset := by
  exact sub_eq_zero.mp (residuals (.asset 1))

/-- The live fee in the production balance residual equals the fee in the
maintained opened-column model.  This is an integer equality, not merely an
equality modulo M31. -/
theorem fee_eq_of_public_residuals
    (fields : TerminalSpendFields) (opened : OpenedColumns)
    (feeBound : fields.fee < 2 ^ 30)
    (constraints : ConstraintsSatisfied opened)
    (residuals : ProductionPublicResidualsVanish fields opened) :
    opened.f = fields.fee := by
  have feeResidual := residuals .feeBalance
  have fieldFee : (opened.f : F) = (fields.fee : F) := by
    have modelFee :
        opened.rin.value - opened.rout.value = (opened.f : F) := by
      rw [constraints.balance]
      ring
    have liveFee :
        opened.rin.value - opened.rout.value = (fields.fee : F) := by
      change opened.rin.value - opened.rout.value - (fields.fee : F) = 0 at feeResidual
      exact sub_eq_zero.mp feeResidual
    exact modelFee.symm.trans liveFee
  have two30BelowP : 2 ^ 30 < p := by norm_num [p]
  exact nat_of_field_eq (opened.hf.trans two30BelowP)
    (feeBound.trans two30BelowP) fieldFee

/-- Universal six-field result.  Once the exact production public residuals
vanish, the maintained opened columns match all six terminal values. -/
theorem public_residuals_bind_all_six_fields
    (fields : TerminalSpendFields) (opened : OpenedColumns)
    (feeBound : fields.fee < 2 ^ 30)
    (constraints : ConstraintsSatisfied opened)
    (residuals : ProductionPublicResidualsVanish fields opened) :
    OpenedColumnsMatchTerminalSpendFields fields opened := by
  have digests := digest_eq_of_public_residuals fields opened residuals
  exact {
    currentAnchor := digests 0
    nullifier := digests 2
    outputCommitment := digests 3
    outputAnchor := digests 1
    asset := output_asset_eq_of_public_residuals fields opened residuals
    fee := fee_eq_of_public_residuals fields opened feeBound constraints residuals
  }

/-- The useful maintained-statement form of the six-field theorem. -/
theorem public_residuals_bind_statement
    (statement : V5PublicStatement) (opened : OpenedColumns)
    (constraints : ConstraintsSatisfied opened)
    (residuals :
      ProductionPublicResidualsVanish (terminalSpendFields statement) opened) :
    OpenedColumnsMatchStatement statement opened := by
  have digests := digest_eq_of_public_residuals
    (terminalSpendFields statement) opened residuals
  exact {
    currentAnchor := digests 0
    nullifier := digests 2
    outputCommitment := digests 3
    outputAnchor := digests 1
    asset := output_asset_eq_of_public_residuals
      (terminalSpendFields statement) opened residuals
    fee := fee_eq_of_public_residuals
      (terminalSpendFields statement) opened statement.feeBound constraints residuals
  }

/-- Row-explicit form used by the production bridge. -/
theorem extracted_public_rows_bind_statement
    (statement : V5PublicStatement) (opened : OpenedColumns)
    (constraints : ConstraintsSatisfied opened)
    (rows : ProductionPublicRowValues)
    (extracted : ExtractedProductionPublicResiduals
      (terminalSpendFields statement) opened rows) :
    OpenedColumnsMatchStatement statement opened :=
  public_residuals_bind_statement statement opened constraints
    (normalized_residuals_of_extracted_rows
      (terminalSpendFields statement) opened rows extracted)

/-- Fixed-trace form used by an accepted-execution proof.  The table `z` is
chosen by the authenticated trace extraction, not by this theorem. -/
theorem extracted_production_trace_binds_statement
    (statement : V5PublicStatement) (opened : OpenedColumns)
    (constraints : ConstraintsSatisfied opened)
    (z : Fin 1024 → Fin 16 → F)
    (extracted : ExtractedProductionTracePublicResiduals
      (terminalSpendFields statement) opened z) :
    OpenedColumnsMatchStatement statement opened :=
  extracted_public_rows_bind_statement statement opened constraints
    (productionPublicRowsFromTrace z) extracted

/-- Conversely, exact statement matching plus the maintained arithmetic
constraints makes every production public row residual zero.  Together with
`public_residuals_bind_statement`, this shows that the residual premise has
exactly the intended six-field content. -/
theorem public_residuals_vanish_of_statement_match
    (statement : V5PublicStatement) (opened : OpenedColumns)
    (constraints : ConstraintsSatisfied opened)
    (hmatch : OpenedColumnsMatchStatement statement opened) :
    ProductionPublicResidualsVanish (terminalSpendFields statement) opened := by
  intro coordinate
  cases coordinate with
  | feeBalance =>
      simp only [publicResidual, terminalSpendFields]
      rw [constraints.balance, hmatch.fee]
      ring
  | digest which limb =>
      fin_cases which
      · simp only [publicResidual, openedDigestField, terminalDigestField,
          terminalSpendFields]
        rw [hmatch.currentAnchor]
        ring
      · simp only [publicResidual, openedDigestField, terminalDigestField,
          terminalSpendFields]
        rw [hmatch.outputAnchor]
        ring
      · simp only [publicResidual, openedDigestField, terminalDigestField,
          terminalSpendFields]
        rw [hmatch.nullifier]
        ring
      · simp only [publicResidual, openedDigestField, terminalDigestField,
          terminalSpendFields]
        rw [hmatch.outputCommitment]
        ring
  | asset which =>
      fin_cases which
      · change opened.a_in - statement.asset = 0
        rw [constraints.assetIn, hmatch.asset]
        ring
      · change opened.a - statement.asset = 0
        rw [hmatch.asset]
        ring

theorem public_residuals_vanish_iff_statement_match
    (statement : V5PublicStatement) (opened : OpenedColumns)
    (constraints : ConstraintsSatisfied opened) :
    ProductionPublicResidualsVanish (terminalSpendFields statement) opened ↔
      OpenedColumnsMatchStatement statement opened :=
  ⟨public_residuals_bind_statement statement opened constraints,
    public_residuals_vanish_of_statement_match statement opened constraints⟩

#print axioms terminal_digest_rows_are_exact
#print axioms public_residual_coordinate_count
#print axioms terminal_asset_rows_are_exact
#print axioms terminal_public_semantic_positions_are_exact
#print axioms projected_row_residual_eq
#print axioms normalized_residuals_of_extracted_rows
#print axioms digest_eq_of_public_residuals
#print axioms output_asset_eq_of_public_residuals
#print axioms fee_eq_of_public_residuals
#print axioms public_residuals_bind_all_six_fields
#print axioms public_residuals_bind_statement
#print axioms extracted_public_rows_bind_statement
#print axioms extracted_production_trace_binds_statement
#print axioms public_residuals_vanish_of_statement_match
#print axioms public_residuals_vanish_iff_statement_match

end AspisV5ProductionPublicResidualBinding
