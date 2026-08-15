import AspisFormal.V5TowerPackedResidualExtraction

/-!
# Exact Boolean-row semantics of the V5 terminal selector

The accepted V5 terminal builds a ten-coordinate multilinear selector.  The
first six coordinates select one of 64 blocks and the final four coordinates
select one of 16 rows in that block.  The production `row` method multiplies
those two weights, using `row >> 4` and `row & 15`.

This file proves the mathematical fact needed by residual extraction: at the
Boolean point belonging to a physical row, the selector is one on that row
and zero on every other row.  The bit order is the production order:
coordinate zero is row bit nine.
-/

namespace AspisV5ProductionRowSelector

open AspisV5TowerPackedResidualExtraction

abbrev TraceRow := Fin 1024
abbrev TerminalPoint (F : Type*) := Fin 10 → F

/-- Production bit order: coordinate zero is the most significant of the ten
physical row bits. -/
def traceRowBit (row : TraceRow) (coordinate : Fin 10) : Bool :=
  Nat.testBit row.val (9 - coordinate.val)

/-- The Boolean terminal point selecting one physical trace row. -/
def booleanPointOfRow {F : Type*} [Zero F] [One F]
    (row : TraceRow) : TerminalPoint F :=
  fun coordinate ↦ if traceRowBit row coordinate then 1 else 0

def rowCoordinateFactor {F : Type*} [CommRing F]
    (point : TerminalPoint F) (row : TraceRow) (coordinate : Fin 10) : F :=
  if traceRowBit row coordinate then point coordinate
  else 1 - point coordinate

/-- Equality-polynomial row weight computed by the terminal's factored
six-coordinate/four-coordinate selector tables. -/
def sourceRowSelector {F : Type*} [CommRing F]
    (point : TerminalPoint F) (row : TraceRow) : F :=
  ∏ coordinate, rowCoordinateFactor point row coordinate

/-- The six-coordinate table entry built by `AtomicSelectors::expand` for
`point[..6]` and read at `row >> 4`. -/
def sourceHighWeight {F : Type*} [CommRing F]
    (point : TerminalPoint F) (row : TraceRow) : F :=
  ∏ coordinate : Fin 6,
    if Nat.testBit (row.val / 16) (5 - coordinate.val) then
      point ⟨coordinate.val, by omega⟩
    else 1 - point ⟨coordinate.val, by omega⟩

/-- The four-coordinate table entry built by `AtomicSelectors::expand` for
`point[6..]` and read at `row & 15`.  For rows below 1024, `row & 15` is
`row % 16`. -/
def sourceLowWeight {F : Type*} [CommRing F]
    (point : TerminalPoint F) (row : TraceRow) : F :=
  ∏ coordinate : Fin 4,
    if Nat.testBit (row.val % 16) (3 - coordinate.val) then
      point ⟨6 + coordinate.val, by omega⟩
    else 1 - point ⟨6 + coordinate.val, by omega⟩

/-- Source-shaped spelling of `AtomicSemanticSelectors::row`: select the
high and low table entries and multiply them. -/
def factoredSourceRowSelector {F : Type*} [CommRing F]
    (point : TerminalPoint F) (row : TraceRow) : F :=
  sourceHighWeight point row * sourceLowWeight point row

theorem source_high_bit_is_trace_bit
    (row : TraceRow) (coordinate : Fin 6) :
    Nat.testBit (row.val / 16) (5 - coordinate.val) =
      traceRowBit row ⟨coordinate.val, by omega⟩ := by
  change Nat.testBit (row.val / 16) (5 - coordinate.val) =
    Nat.testBit row.val (9 - coordinate.val)
  rw [show 16 = 2 ^ 4 by norm_num, Nat.testBit_div_two_pow]
  congr 1
  omega

theorem source_low_bit_is_trace_bit
    (row : TraceRow) (coordinate : Fin 4) :
    Nat.testBit (row.val % 16) (3 - coordinate.val) =
      traceRowBit row ⟨6 + coordinate.val, by omega⟩ := by
  change Nat.testBit (row.val % 16) (3 - coordinate.val) =
    Nat.testBit row.val (9 - (6 + coordinate.val))
  rw [show 16 = 2 ^ 4 by norm_num, Nat.testBit_mod_two_pow]
  have within : 3 - coordinate.val < 4 := by omega
  simp only [within, decide_true, Bool.true_and]
  congr 1
  omega

theorem sourceHighWeight_eq_coordinateFactors
    {F : Type*} [CommRing F] (point : TerminalPoint F) (row : TraceRow) :
    sourceHighWeight point row =
      ∏ coordinate : Fin 6,
        rowCoordinateFactor point row (Fin.castAdd 4 coordinate) := by
  apply Finset.prod_congr rfl
  intro coordinate _
  unfold rowCoordinateFactor
  rw [source_high_bit_is_trace_bit]
  rfl

theorem sourceLowWeight_eq_coordinateFactors
    {F : Type*} [CommRing F] (point : TerminalPoint F) (row : TraceRow) :
    sourceLowWeight point row =
      ∏ coordinate : Fin 4,
        rowCoordinateFactor point row (Fin.natAdd 6 coordinate) := by
  apply Finset.prod_congr rfl
  intro coordinate _
  unfold rowCoordinateFactor
  rw [source_low_bit_is_trace_bit]
  rfl

/-- The source's 64-entry/16-entry factorization is exactly the ordinary
ten-coordinate equality polynomial. -/
theorem factoredSourceRowSelector_eq_sourceRowSelector
    {F : Type*} [CommRing F] (point : TerminalPoint F) (row : TraceRow) :
    factoredSourceRowSelector point row = sourceRowSelector point row := by
  rw [factoredSourceRowSelector, sourceHighWeight_eq_coordinateFactors,
    sourceLowWeight_eq_coordinateFactors]
  unfold sourceRowSelector
  change
    ((∏ coordinate : Fin 6,
        rowCoordinateFactor point row (Fin.castAdd 4 coordinate)) *
      ∏ coordinate : Fin 4,
        rowCoordinateFactor point row (Fin.natAdd 6 coordinate)) =
      ∏ coordinate : Fin (6 + 4), rowCoordinateFactor point row coordinate
  rw [Fin.prod_univ_add]

/-- Ten big-endian bits determine a physical row below 1024. -/
theorem traceRow_ext
    {left right : TraceRow}
    (bits : ∀ coordinate, traceRowBit left coordinate =
      traceRowBit right coordinate) :
    left = right := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit < 10
  · let coordinate : Fin 10 := ⟨9 - bit, by omega⟩
    have hcoordinate := bits coordinate
    have hindex : 9 - coordinate.val = bit := by
      simp only [coordinate]
      omega
    simpa only [traceRowBit, hindex] using hcoordinate
  · have hten : 10 ≤ bit := by omega
    have hleftBound : left.val < 2 ^ bit := by
      calc
        left.val < 2 ^ 10 := by norm_num
        _ ≤ 2 ^ bit := Nat.pow_le_pow_right (by decide) hten
    have hrightBound : right.val < 2 ^ bit := by
      calc
        right.val < 2 ^ 10 := by norm_num
        _ ≤ 2 ^ bit := Nat.pow_le_pow_right (by decide) hten
    rw [Nat.testBit_eq_false_of_lt hleftBound,
      Nat.testBit_eq_false_of_lt hrightBound]

theorem exists_traceRowBit_ne_of_ne
    {left right : TraceRow} (different : left ≠ right) :
    ∃ coordinate, traceRowBit left coordinate ≠ traceRowBit right coordinate := by
  by_contra noDifference
  push Not at noDifference
  exact different (traceRow_ext noDifference)

/-- At its own Boolean point, the source-shaped selector is exactly a
Kronecker delta on all 1,024 rows. -/
theorem sourceRowSelector_at_booleanPoint
    {F : Type*} [CommRing F] (row selected : TraceRow) :
    sourceRowSelector (booleanPointOfRow (F := F) row) selected =
      if selected = row then 1 else 0 := by
  classical
  by_cases same : selected = row
  · subst selected
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro coordinate _
    by_cases bit : traceRowBit row coordinate
    · simp [rowCoordinateFactor, booleanPointOfRow, bit]
    · simp [rowCoordinateFactor, booleanPointOfRow, bit]
  · rw [if_neg same]
    obtain ⟨coordinate, differs⟩ := exists_traceRowBit_ne_of_ne same
    apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
    cases selectedBit : traceRowBit selected coordinate <;>
      cases rowBit : traceRowBit row coordinate
    · exact (differs (by simp [selectedBit, rowBit])).elim
    · simp [rowCoordinateFactor, booleanPointOfRow, selectedBit, rowBit]
    · simp [rowCoordinateFactor, booleanPointOfRow, selectedBit, rowBit]
    · exact (differs (by simp [selectedBit, rowBit])).elim

/-- The factored source formula is one on its selected Boolean row and zero on
every other row.  This algebraic statement needs only a commutative ring. -/
theorem factoredSourceRowSelector_at_booleanPoint
    {F : Type*} [CommRing F] (row selected : TraceRow) :
    factoredSourceRowSelector (booleanPointOfRow (F := F) row) selected =
      if selected = row then 1 else 0 := by
  rw [factoredSourceRowSelector_eq_sourceRowSelector]
  exact sourceRowSelector_at_booleanPoint row selected

/-- The exact selector obligation used by the tower-packed residual theorem. -/
theorem sourceRowSelector_selectsExactRow {F : Type*} [Field F] :
    SelectsExactRow (sourceRowSelector (F := F))
      (booleanPointOfRow (F := F)) := by
  exact sourceRowSelector_at_booleanPoint

/-- The source's actual two-table spelling therefore selects exactly one
Boolean row as well. -/
theorem factoredSourceRowSelector_selectsExactRow
    {F : Type*} [Field F] :
    SelectsExactRow (factoredSourceRowSelector (F := F))
      (booleanPointOfRow (F := F)) := by
  exact factoredSourceRowSelector_at_booleanPoint

/-- A source-extracted selector discharges the generic selector boundary as
soon as its returned field value is identified with the exact factored source
formula above.  This keeps the executable-loop correspondence separate from
the already-closed Boolean algebra. -/
theorem extractedSelector_selectsExactRow_of_eq
    {F : Type*} [Field F]
    (rustSelector : TerminalPoint F → TraceRow → F)
    (agreement : rustSelector = factoredSourceRowSelector) :
    SelectsExactRow rustSelector (booleanPointOfRow (F := F)) := by
  rw [agreement]
  exact factoredSourceRowSelector_selectsExactRow

#print axioms traceRow_ext
#print axioms sourceRowSelector_at_booleanPoint
#print axioms factoredSourceRowSelector_at_booleanPoint
#print axioms sourceRowSelector_selectsExactRow
#print axioms factoredSourceRowSelector_selectsExactRow
#print axioms extractedSelector_selectsExactRow_of_eq

end AspisV5ProductionRowSelector
