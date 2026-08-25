import AspisFormal.Pool.V7OpenedColumnsFromTrace
import AspisFormal.V5ProductionPublicResidualBinding
import AspisFormal.V5AcceptedSpendRelation
import AspisFormal.V5TowerPackedResidualExtraction

/-!
# Tag-73 atomic semantic rows from the physical trace

This leaf is the Boolean-row model of the 77 source semantic positions in
`atomic_state_only_terminal.rs::atomic_semantic_packed_impl`.  It does not
model Poseidon rows or the compiled copy/LogUp lane.  Those two families are
parameters of `constraintRowsWithAtomicSemantic`, so neither is replaced by
fake zero residuals.

The source positions are exactly:

* `0..15`: retained/path initial-state residuals;
* `16..31`: absorption-zero residuals (positions 16 and 17 have empty support);
* `32..61`: three groups of ten bitness residuals;
* `62..64`: the three ten-bit reconstructions;
* `65`: the three-limb reconstruction;
* `66`: fee balance;
* `67..74`: four row-selected public digests sharing eight positions; and
* `75..76`: input and output assets.

Only exact Boolean row numbers are used.  No claim is made here about the
off-domain factorized selector polynomial.  The one copy fact needed to turn
the fee row into the normalized output range value is isolated as
`BalanceOutputCellAlias`; the larger `RequiredTraceAliases` record and path
bit typing are not assumed.
-/

set_option autoImplicit false

namespace AspisPool.V7AtomicSemanticRowsFromTrace

open AspisFormal.ArithmetizationCore
open AspisPool.V7OpenedColumnsFromTrace
open AspisV5AcceptedSpendRelation
open AspisV5ProductionPublicResidualBinding
open AspisV5TowerPackedResidualExtraction

/-! ## The exact 77-position inventory -/

/-- One source semantic position before four-at-a-time tower packing. -/
inductive AtomicSemanticCoordinate where
  | initial (column : Fin 16)
  | absorption (column : Fin 16)
  | rangeBit (view : Fin 3) (bit : Fin 10)
  | rangeReconstruction (view : Fin 3)
  | rangeTriple
  | feeBalance
  | digest (limb : Fin 8)
  | asset (which : Fin 2)
  deriving DecidableEq, Fintype

/-- Exact source position used by `atomic_accumulate`/`atomic_add_preweighted`. -/
def semanticPosition : AtomicSemanticCoordinate → Nat
  | .initial column => column.val
  | .absorption column => 16 + column.val
  | .rangeBit view bit => 32 + 10 * view.val + bit.val
  | .rangeReconstruction view => 62 + view.val
  | .rangeTriple => 65
  | .feeBalance => 66
  | .digest limb => 67 + limb.val
  | .asset which => 75 + which.val

theorem atomic_semantic_coordinate_count :
    Fintype.card AtomicSemanticCoordinate = 77 := by
  decide

theorem semanticPosition_lt_seventy_seven
    (coordinate : AtomicSemanticCoordinate) :
    semanticPosition coordinate < 77 := by
  cases coordinate <;> simp only [semanticPosition] <;> omega

theorem semanticPosition_injective : Function.Injective semanticPosition := by
  decide

/-- Packed QM31 lane occupied by one source position. -/
def semanticPackedLane (coordinate : AtomicSemanticCoordinate) : Fin 20 :=
  ⟨semanticPosition coordinate / 4, by
    have := semanticPosition_lt_seventy_seven coordinate
    omega⟩

/-- Tower-basis slot occupied inside the packed lane. -/
def semanticPackedSlot (coordinate : AtomicSemanticCoordinate) : Fin 4 :=
  ⟨semanticPosition coordinate % 4, Nat.mod_lt _ (by decide)⟩

def semanticPackedLocation
    (coordinate : AtomicSemanticCoordinate) : Fin 20 × Fin 4 :=
  (semanticPackedLane coordinate, semanticPackedSlot coordinate)

theorem semanticPackedLocation_recovers_position
    (coordinate : AtomicSemanticCoordinate) :
    4 * (semanticPackedLane coordinate).val +
        (semanticPackedSlot coordinate).val =
      semanticPosition coordinate := by
  simp only [semanticPackedLane, semanticPackedSlot]
  omega

theorem semanticPackedLocation_injective :
    Function.Injective semanticPackedLocation := by
  intro left right equal
  apply semanticPosition_injective
  have recovered := congrArg
    (fun location : Fin 20 × Fin 4 =>
      4 * location.1.val + location.2.val) equal
  simpa [semanticPackedLocation,
    semanticPackedLocation_recovers_position] using recovered

/-! ## Frozen Boolean-row supports -/

/-- Atomic-retained entries `INITIAL_BLOCKS[0,1,22,23]`. -/
def retainedInitialRow : Fin 4 → Fin 1024 := ![0, 16, 704, 736]

def retainedInitialDomain : Fin 4 → F :=
  ![1095958529, 1095958531, 1095958530, 1095958531]

def retainedInitialLength : Fin 4 → F := ![8, 18, 16, 18]

/-- Row zero of atomic path blocks 4 through 43. -/
def pathInitialRow (block : Fin 40) : Fin 1024 :=
  ⟨16 * (block.val + 4), by omega⟩

/-- Low-lane absorption support: blocks 3 and 48, local row 12. -/
def absorptionLowRow : Fin 2 → Fin 1024 := ![60, 780]

/-- High-lane absorption support: blocks 1, 44, 45, 46, and 48. -/
def absorptionHighRow : Fin 5 → Fin 1024 := ![28, 716, 732, 748, 780]

/-- The only rows selected by the shared range polynomial. -/
def rangeBaseRow : Fin 2 → Fin 1024 := ![864, 866]

/-- The exact `z`, `succ(z)`, and `xor12(z)` physical rows. -/
def rangeViewRow : Fin 2 → Fin 3 → Fin 1024
  | 0 => inputRangeRow
  | 1 => outputRangeRow

/-- Four digest supports `[23,43,45,48] * 16 + 11`. -/
def digestRow : Fin 4 → Fin 1024 := ![379, 699, 731, 779]

def assetRow : Fin 2 → Fin 1024 := ![795, 799]

theorem retained_initial_rows_are_exact :
    List.ofFn (fun which : Fin 4 => (retainedInitialRow which).val) =
      [0, 16, 704, 736] := by
  decide

theorem absorption_rows_are_exact :
    List.ofFn (fun which : Fin 2 => (absorptionLowRow which).val) = [60, 780] ∧
      List.ofFn (fun which : Fin 5 => (absorptionHighRow which).val) =
        [28, 716, 732, 748, 780] := by
  decide

theorem range_digest_asset_rows_are_exact :
    List.ofFn (fun which : Fin 2 => (rangeBaseRow which).val) = [864, 866] ∧
      List.ofFn (fun which : Fin 4 => (digestRow which).val) =
        [379, 699, 731, 779] ∧
      List.ofFn (fun which : Fin 2 => (assetRow which).val) = [795, 799] := by
  decide

/-- Exact row-support predicate; unsupported positions are structural zeros. -/
def semanticSupportsRow
    (coordinate : AtomicSemanticCoordinate) (row : Fin 1024) : Prop :=
  match coordinate with
  | .initial column =>
      (∃ which, row = retainedInitialRow which) ∨
        (column.val < 8 ∧ ∃ block, row = pathInitialRow block)
  | .absorption column =>
      (2 ≤ column.val ∧ column.val < 8 ∧
        ∃ which, row = absorptionLowRow which) ∨
      (8 ≤ column.val ∧ ∃ which, row = absorptionHighRow which)
  | .rangeBit _ _ | .rangeReconstruction _ | .rangeTriple =>
      row = rangeBaseRow 0 ∨ row = rangeBaseRow 1
  | .feeBalance => row = 864
  | .digest _ => ∃ which, row = digestRow which
  | .asset which => row = assetRow which

/-! ## Source residual formulas -/

def initialExpected (which : Fin 4) (column : Fin 16) : F :=
  if column = 8 then retainedInitialDomain which
  else if column = 9 then retainedInitialLength which
  else 0

/-- Retained and path initial selectors evaluated at one Boolean row. -/
def initialResidual
    (trace : PhysicalTrace) (row : Fin 1024) (column : Fin 16) : F :=
  (∑ which : Fin 4,
    if row = retainedInitialRow which then
      trace row column - initialExpected which column
    else 0) +
  if column.val < 8 then
    ∑ block : Fin 40,
      if row = pathInitialRow block then trace row column else 0
  else 0

/-- The exact `0x00fc`, `0xff00`, and `0xfffc` Boolean-row supports. -/
def absorptionResidual
    (trace : PhysicalTrace) (row : Fin 1024) (column : Fin 16) : F :=
  (if 2 ≤ column.val ∧ column.val < 8 then
    ∑ which : Fin 2,
      if row = absorptionLowRow which then trace row column else 0
   else 0) +
  (if 8 ≤ column.val then
    ∑ which : Fin 5,
      if row = absorptionHighRow which then trace row column else 0
   else 0)

/-- Exact little-endian ten-bit reconstruction used by `atomic_reconstruct_10`. -/
def reconstructTenAt (trace : PhysicalTrace) (row : Fin 1024) : F :=
  ∑ bit : Fin 10,
    trace row (rangeBitColumn bit) * (2 : F) ^ (bit : Nat)

def rangeBitResidualAt
    (trace : PhysicalTrace) (which : Fin 2) (view : Fin 3) (bit : Fin 10) : F :=
  let value := trace (rangeViewRow which view) (rangeBitColumn bit)
  value * (value - 1)

def rangeReconstructionResidualAt
    (trace : PhysicalTrace) (which : Fin 2) (view : Fin 3) : F :=
  trace (rangeViewRow which view) 10 -
    reconstructTenAt trace (rangeViewRow which view)

/-- Three limbs at weights `1`, `2^10`, and `2^20`. -/
def rangeTripleResidualAt (trace : PhysicalTrace) (which : Fin 2) : F :=
  trace (rangeViewRow which 0) 11 -
    ∑ view : Fin 3,
      trace (rangeViewRow which view) 10 * (2 : F) ^ (10 * view.val)

def digestResidualAt
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (limb : Fin 8) (row : Fin 1024) : F :=
  if row = digestRow 0 then trace row ⟨limb.val, by omega⟩ - fields.currentAnchor limb
  else if row = digestRow 1 then trace row ⟨limb.val, by omega⟩ - fields.outputAnchor limb
  else if row = digestRow 2 then trace row ⟨limb.val, by omega⟩ - fields.nullifier limb
  else if row = digestRow 3 then
    trace row ⟨limb.val, by omega⟩ - fields.outputCommitment limb
  else 0

/-- Complete source residual at one Boolean trace row. -/
def atomicSemanticResidual
    (fields : TerminalSpendFields) (trace : PhysicalTrace) :
    AtomicSemanticCoordinate → Fin 1024 → F
  | .initial column, row => initialResidual trace row column
  | .absorption column, row => absorptionResidual trace row column
  | .rangeBit view bit, row =>
      if row = rangeBaseRow 0 then rangeBitResidualAt trace 0 view bit
      else if row = rangeBaseRow 1 then rangeBitResidualAt trace 1 view bit
      else 0
  | .rangeReconstruction view, row =>
      if row = rangeBaseRow 0 then rangeReconstructionResidualAt trace 0 view
      else if row = rangeBaseRow 1 then rangeReconstructionResidualAt trace 1 view
      else 0
  | .rangeTriple, row =>
      if row = rangeBaseRow 0 then rangeTripleResidualAt trace 0
      else if row = rangeBaseRow 1 then rangeTripleResidualAt trace 1
      else 0
  | .feeBalance, row =>
      if row = 864 then
        trace row 11 - trace row 12 - (fields.fee : F)
      else 0
  | .digest limb, row => digestResidualAt fields trace limb row
  | .asset which, row =>
      if row = assetRow which then trace row 1 - fields.asset else 0

@[simp] theorem range_bit_residual_at_base
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (which : Fin 2) (view : Fin 3) (bit : Fin 10) :
    atomicSemanticResidual fields trace (.rangeBit view bit)
        (rangeBaseRow which) =
      rangeBitResidualAt trace which view bit := by
  fin_cases which <;> simp [atomicSemanticResidual, rangeBaseRow]

@[simp] theorem range_reconstruction_residual_at_base
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (which : Fin 2) (view : Fin 3) :
    atomicSemanticResidual fields trace (.rangeReconstruction view)
        (rangeBaseRow which) =
      rangeReconstructionResidualAt trace which view := by
  fin_cases which <;> simp [atomicSemanticResidual, rangeBaseRow]

@[simp] theorem range_triple_residual_at_base
    (fields : TerminalSpendFields) (trace : PhysicalTrace) (which : Fin 2) :
    atomicSemanticResidual fields trace .rangeTriple (rangeBaseRow which) =
      rangeTripleResidualAt trace which := by
  fin_cases which <;> simp [atomicSemanticResidual, rangeBaseRow]

@[simp] theorem fee_residual_at_row_864
    (fields : TerminalSpendFields) (trace : PhysicalTrace) :
    atomicSemanticResidual fields trace .feeBalance 864 =
      trace 864 11 - trace 864 12 - (fields.fee : F) := by
  simp [atomicSemanticResidual]

@[simp] theorem digest_residual_at_selected_row
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (which : Fin 4) (limb : Fin 8) :
    atomicSemanticResidual fields trace (.digest limb) (digestRow which) =
      trace (digestRow which) ⟨limb.val, by omega⟩ -
        terminalDigestField fields which limb := by
  fin_cases which <;>
    simp [atomicSemanticResidual, digestResidualAt, digestRow,
      terminalDigestField]

@[simp] theorem asset_residual_at_selected_row
    (fields : TerminalSpendFields) (trace : PhysicalTrace) (which : Fin 2) :
    atomicSemanticResidual fields trace (.asset which) (assetRow which) =
      trace (assetRow which) 1 - fields.asset := by
  simp [atomicSemanticResidual]

/-! ## Exact four-at-a-time source packing -/

/-- Base-field coordinates underlying the twenty packed semantic lanes. -/
def atomicSemanticRowsFromTrace
    (fields : TerminalSpendFields) (trace : PhysicalTrace) :
    Fin 1024 → Fin 20 → Fin 4 → F :=
  fun row group slot =>
    ∑ coordinate : AtomicSemanticCoordinate,
      if semanticPackedLocation coordinate = (group, slot) then
        atomicSemanticResidual fields trace coordinate row
      else 0

/-- Every one of the 77 source coordinates is recovered at its exact packed
lane and tower slot. -/
theorem atomicSemanticRows_at_coordinate
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (coordinate : AtomicSemanticCoordinate) (row : Fin 1024) :
    atomicSemanticRowsFromTrace fields trace row
        (semanticPackedLane coordinate) (semanticPackedSlot coordinate) =
      atomicSemanticResidual fields trace coordinate row := by
  classical
  unfold atomicSemanticRowsFromTrace
  rw [Finset.sum_eq_single coordinate]
  · simp [semanticPackedLocation]
  · intro other _ different
    have locationDifferent :
        semanticPackedLocation other ≠ semanticPackedLocation coordinate := by
      intro equal
      exact different (semanticPackedLocation_injective equal)
    have targetDifferent :
        semanticPackedLocation other ≠
          (semanticPackedLane coordinate, semanticPackedSlot coordinate) := by
      simpa [semanticPackedLocation] using locationDifferent
    simp [targetDifferent]
  · simp

def AtomicSemanticRowsVanish
    (fields : TerminalSpendFields) (trace : PhysicalTrace) : Prop :=
  ∀ row group slot, atomicSemanticRowsFromTrace fields trace row group slot = 0

theorem coordinate_residual_zero_of_semantic_rows_vanish
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace)
    (coordinate : AtomicSemanticCoordinate) (row : Fin 1024) :
    atomicSemanticResidual fields trace coordinate row = 0 := by
  rw [← atomicSemanticRows_at_coordinate fields trace coordinate row]
  exact vanish row (semanticPackedLane coordinate) (semanticPackedSlot coordinate)

/-! ## Poseidon and compiled copy remain separate -/

/-- Install only the semantic family modeled above.  The caller supplies the
independent Poseidon rows and the extension-field compiled copy/LogUp lane. -/
def constraintRowsWithAtomicSemantic
    {K : Type*} [Field K] [Algebra F K]
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (compiledCopyLane : Fin 1024 → K) :
    Fin 1024 → ConstraintRowResiduals (F := F) (K := K) :=
  fun row => {
    poseidon := poseidonRows row
    semantic := atomicSemanticRowsFromTrace fields trace row
    copy := compiledCopyLane row
  }

/-! ## Exact public-row correspondence -/

def atomicCoordinateOfPublic :
    PublicResidualCoordinate → AtomicSemanticCoordinate
  | .feeBalance => .feeBalance
  | .digest _ limb => .digest limb
  | .asset which => .asset which

@[simp] theorem atomicCoordinateOfPublic_packedLane
    (coordinate : PublicResidualCoordinate) :
    semanticPackedLane (atomicCoordinateOfPublic coordinate) =
      publicResidualPackedLane coordinate := by
  cases coordinate <;> rfl

@[simp] theorem atomicCoordinateOfPublic_packedSlot
    (coordinate : PublicResidualCoordinate) :
    semanticPackedSlot (atomicCoordinateOfPublic coordinate) =
      publicResidualPackedSlot coordinate := by
  cases coordinate <;> rfl

theorem atomic_public_coordinate_residual_eq
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (coordinate : PublicResidualCoordinate) :
    atomicSemanticResidual fields trace (atomicCoordinateOfPublic coordinate)
        (publicResidualTraceRow coordinate) =
      rowPublicResidual fields (productionPublicRowsFromTrace trace) coordinate := by
  cases coordinate with
  | feeBalance =>
      rfl
  | digest which limb =>
      fin_cases which <;>
        simp [atomicCoordinateOfPublic, atomicSemanticResidual,
          digestResidualAt, publicResidualTraceRow,
          publicResidualRow, terminalDigestRow, digestRow,
          terminalDigestField, productionPublicRowsFromTrace, rowPublicResidual]
  | asset which =>
      fin_cases which <;>
        simp [atomicCoordinateOfPublic, atomicSemanticResidual,
          publicResidualTraceRow,
          publicResidualRow, assetRow, productionPublicRowsFromTrace,
          rowPublicResidual]

theorem productionPublicResiduals_match_atomic_semantic_rows
    {K : Type*} [Field K] [Algebra F K]
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (compiledCopyLane : Fin 1024 → K) :
    ProductionPublicResidualsMatchConstraintRows fields
      (productionPublicRowsFromTrace trace)
      (constraintRowsWithAtomicSemantic fields trace poseidonRows
        compiledCopyLane) where
  residual := by
    intro coordinate
    change atomicSemanticRowsFromTrace fields trace
        (publicResidualTraceRow coordinate)
        (publicResidualPackedLane coordinate)
        (publicResidualPackedSlot coordinate) =
      rowPublicResidual fields (productionPublicRowsFromTrace trace) coordinate
    rw [← atomicCoordinateOfPublic_packedLane coordinate,
      ← atomicCoordinateOfPublic_packedSlot coordinate,
      atomicSemanticRows_at_coordinate]
    exact atomic_public_coordinate_residual_eq fields trace coordinate

theorem public_row_residuals_vanish_of_atomic_semantic_rows
    (fields : TerminalSpendFields) (trace : PhysicalTrace)
    (vanish : AtomicSemanticRowsVanish fields trace) :
    ProductionPublicRowResidualsVanish fields
      (productionPublicRowsFromTrace trace) := by
  intro coordinate
  rw [← atomic_public_coordinate_residual_eq fields trace coordinate]
  exact coordinate_residual_zero_of_semantic_rows_vanish fields trace vanish
    (atomicCoordinateOfPublic coordinate) (publicResidualTraceRow coordinate)

/-! ## The one arithmetic copy alias -/

/-- The fee row reads output value from `(864,12)`, while `rout.value` is
physically `(866,11)`.  This is exactly one compiled-copy equality. -/
def BalanceOutputCellAlias (trace : PhysicalTrace) : Prop :=
  trace 864 12 = trace 866 11

theorem balanceOutputCellAlias_iff_raw_alias (trace : PhysicalTrace) :
    BalanceOutputCellAlias trace ↔
      (rawOpenedColumnsFromTrace trace).balanceOutputValue =
        (rawOpenedColumnsFromTrace trace).rout.value := by
  rfl

def boundedFeeFromStatement (statement : V5PublicStatement) : BoundedFee :=
  ⟨statement.fee, statement.feeBound⟩

theorem production_public_rows_project_to_opened_columns
    (statement : V5PublicStatement) (trace : PhysicalTrace)
    (balanceAlias : BalanceOutputCellAlias trace) :
    ProductionPublicRowsProjectToOpenedColumns
      (productionPublicRowsFromTrace trace)
      (openedColumnsFromTrace trace (boundedFeeFromStatement statement)) where
  inputValue := rfl
  outputValue := balanceAlias
  digest := by
    intro which
    fin_cases which <;> rfl
  asset := by
    intro which
    fin_cases which <;> rfl

/-! ## The 45-coordinate range and public consequence -/

theorem arithmetic_residuals_of_atomic_semantic_rows
    (statement : V5PublicStatement) (trace : PhysicalTrace)
    (balanceAlias : BalanceOutputCellAlias trace)
    (vanish : AtomicSemanticRowsVanish
      (terminalSpendFields statement) trace) :
    ExtractedArithmeticResiduals
      (openedColumnsFromTrace trace (boundedFeeFromStatement statement)) where
  rangeInBit := by
    intro view bit
    change trace (inputRangeRow view) (rangeBitColumn bit) *
      (trace (inputRangeRow view) (rangeBitColumn bit) - 1) = 0
    have residual := coordinate_residual_zero_of_semantic_rows_vanish
      (terminalSpendFields statement) trace vanish (.rangeBit view bit) 864
    change atomicSemanticResidual (terminalSpendFields statement) trace
      (.rangeBit view bit) (rangeBaseRow 0) = 0 at residual
    rw [range_bit_residual_at_base] at residual
    exact residual
  rangeInLimb := by
    intro view
    change trace (inputRangeRow view) 10 -
      (∑ bit : Fin 10,
        trace (inputRangeRow view) (rangeBitColumn bit) *
          (2 : F) ^ (bit : Nat)) = 0
    have residual := coordinate_residual_zero_of_semantic_rows_vanish
      (terminalSpendFields statement) trace vanish
      (.rangeReconstruction view) 864
    change atomicSemanticResidual (terminalSpendFields statement) trace
      (.rangeReconstruction view) (rangeBaseRow 0) = 0 at residual
    rw [range_reconstruction_residual_at_base] at residual
    exact residual
  rangeInValue := by
    change trace 864 11 -
      (∑ view : Fin 3,
        trace (inputRangeRow view) 10 *
          (2 : F) ^ (10 * (view : Nat))) = 0
    have residual := coordinate_residual_zero_of_semantic_rows_vanish
      (terminalSpendFields statement) trace vanish .rangeTriple 864
    change atomicSemanticResidual (terminalSpendFields statement) trace
      .rangeTriple (rangeBaseRow 0) = 0 at residual
    rw [range_triple_residual_at_base] at residual
    exact residual
  rangeOutBit := by
    intro view bit
    change trace (outputRangeRow view) (rangeBitColumn bit) *
      (trace (outputRangeRow view) (rangeBitColumn bit) - 1) = 0
    have residual := coordinate_residual_zero_of_semantic_rows_vanish
      (terminalSpendFields statement) trace vanish (.rangeBit view bit) 866
    change atomicSemanticResidual (terminalSpendFields statement) trace
      (.rangeBit view bit) (rangeBaseRow 1) = 0 at residual
    rw [range_bit_residual_at_base] at residual
    exact residual
  rangeOutLimb := by
    intro view
    change trace (outputRangeRow view) 10 -
      (∑ bit : Fin 10,
        trace (outputRangeRow view) (rangeBitColumn bit) *
          (2 : F) ^ (bit : Nat)) = 0
    have residual := coordinate_residual_zero_of_semantic_rows_vanish
      (terminalSpendFields statement) trace vanish
      (.rangeReconstruction view) 866
    change atomicSemanticResidual (terminalSpendFields statement) trace
      (.rangeReconstruction view) (rangeBaseRow 1) = 0 at residual
    rw [range_reconstruction_residual_at_base] at residual
    exact residual
  rangeOutValue := by
    change trace 866 11 -
      (∑ view : Fin 3,
        trace (outputRangeRow view) 10 *
          (2 : F) ^ (10 * (view : Nat))) = 0
    have residual := coordinate_residual_zero_of_semantic_rows_vanish
      (terminalSpendFields statement) trace vanish .rangeTriple 866
    change atomicSemanticResidual (terminalSpendFields statement) trace
      .rangeTriple (rangeBaseRow 1) = 0 at residual
    rw [range_triple_residual_at_base] at residual
    exact residual
  balance := by
    have residual := coordinate_residual_zero_of_semantic_rows_vanish
      (terminalSpendFields statement) trace vanish .feeBalance 864
    rw [fee_residual_at_row_864] at residual
    rw [balanceAlias] at residual
    change trace 864 11 - trace 866 11 - (statement.fee : F) = 0 at residual
    change trace 864 11 - (trace 866 11 + (statement.fee : F)) = 0
    linear_combination residual
  asset := by
    have inputResidual := coordinate_residual_zero_of_semantic_rows_vanish
      (terminalSpendFields statement) trace vanish (.asset 0) 795
    have outputResidual := coordinate_residual_zero_of_semantic_rows_vanish
      (terminalSpendFields statement) trace vanish (.asset 1) 799
    have inputEq : trace 795 1 = statement.asset := by
      apply sub_eq_zero.mp
      simpa [atomicSemanticResidual, assetRow, terminalSpendFields] using inputResidual
    have outputEq : trace 799 1 = statement.asset := by
      apply sub_eq_zero.mp
      simpa [atomicSemanticResidual, assetRow, terminalSpendFields] using outputResidual
    change trace 795 1 - trace 799 1 = 0
    exact sub_eq_zero.mpr (inputEq.trans outputEq.symm)

theorem production_public_residuals_vanish_of_atomic_semantic_rows
    (statement : V5PublicStatement) (trace : PhysicalTrace)
    (balanceAlias : BalanceOutputCellAlias trace)
    (vanish : AtomicSemanticRowsVanish
      (terminalSpendFields statement) trace) :
    ProductionPublicResidualsVanish (terminalSpendFields statement)
      (openedColumnsFromTrace trace (boundedFeeFromStatement statement)) := by
  apply normalized_residuals_of_extracted_rows
    (terminalSpendFields statement)
    (openedColumnsFromTrace trace (boundedFeeFromStatement statement))
    (productionPublicRowsFromTrace trace)
  exact {
    projects := production_public_rows_project_to_opened_columns
      statement trace balanceAlias
    vanish := public_row_residuals_vanish_of_atomic_semantic_rows
      (terminalSpendFields statement) trace vanish
  }

theorem public_fields_match_of_atomic_semantic_rows
    (statement : V5PublicStatement) (trace : PhysicalTrace)
    (balanceAlias : BalanceOutputCellAlias trace)
    (vanish : AtomicSemanticRowsVanish
      (terminalSpendFields statement) trace) :
    OpenedColumnsMatchStatement statement
      (openedColumnsFromTrace trace (boundedFeeFromStatement statement)) := by
  apply public_residuals_bind_statement statement
    (openedColumnsFromTrace trace (boundedFeeFromStatement statement))
  · exact (arithmetic_residuals_of_atomic_semantic_rows
      statement trace balanceAlias vanish).toConstraintsSatisfied
  · exact production_public_residuals_vanish_of_atomic_semantic_rows
      statement trace balanceAlias vanish

/-! ## Audit -/

#print axioms semanticPosition_injective
#print axioms atomicSemanticRows_at_coordinate
#print axioms productionPublicResiduals_match_atomic_semantic_rows
#print axioms production_public_rows_project_to_opened_columns
#print axioms arithmetic_residuals_of_atomic_semantic_rows
#print axioms public_fields_match_of_atomic_semantic_rows

end AspisPool.V7AtomicSemanticRowsFromTrace
