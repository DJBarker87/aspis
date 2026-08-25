import AspisFormal.ArithmetizationCore

/-!
# Exact V7 physical-trace projection into `OpenedColumns`

This file records the smallest honest bridge from the deployed 1,024-by-16
M31 C1 table to `ArithmetizationCore.OpenedColumns`.

The coordinate inventory is the literal atomic state-only layout:

* `state_only_trace.rs:35-40, 950-956` fixes the two three-row direct-range
  triples and writes their ten bit cells plus limb reconstruction cell;
* `atomic_state_only_trace.rs:28-39, 51-59, 205-213` fixes the 49-block
  schedule, local final row 11, and eight-limb digest truncation;
* `atomic_state_only_trace.rs:275-320` writes all three path-bit aliases and
  the one shared sibling digest into the generated auxiliary layout;
* `atomic_state_only_registry.rs:269-373` deterministically allocates those
  auxiliary cells;
* `state_only_trace.rs:780-806` remaps the retained private witness sources;
* `atomic_state_only_terminal.rs:1164-1221` consumes the direct-range,
  balance, four public-digest, and two asset cells.

Two distinctions must remain visible.

1. The trace has separate output-range `(866,11)`, output-note `(799,0)`, and
   balance `(864,12)` cells. The compiled copy links at
   `atomic_state_only_terminal_constants.rs:72-74` are what identify them.
2. A path direction is stored as M31 in three cells. A `Bool` is recovered
   exactly only when the selected field cell is zero or one. The decoder below
   is accompanied by an iff theorem; it is not an unchecked coercion.

Finally, the public fee is not in C1 at all. The terminal reads
`statement.spend.fee` directly at `atomic_state_only_terminal.rs:1192-1197`.
Consequently a raw trace cannot construct the complete dependent
`OpenedColumns.f/hf` pair. `BoundedFee` is the precise additional typed datum,
and `trace_does_not_determine_fee` proves the obstruction rather than hiding it
behind choice.
-/

set_option autoImplicit false

namespace AspisPool.V7OpenedColumnsFromTrace

open AspisFormal.ArithmetizationCore

/-- The exact base-field table reconstructed by the V7 C1 extractor. -/
abbrev PhysicalTrace := Fin 1024 → Fin 16 → F

/-! ## Frozen physical coordinates -/

/-- Input direct-range rows: `z`, `succ(z)`, and `xor12(z)`. -/
def inputRangeRow : Fin 3 → Fin 1024 := ![864, 865, 876]

/-- Output direct-range rows: `z`, `succ(z)`, and `xor12(z)`. -/
def outputRangeRow : Fin 3 → Fin 1024 := ![866, 867, 878]

/-- The ten direct-range bit columns. -/
def rangeBitColumn (bit : Fin 10) : Fin 16 :=
  ⟨bit.val, by omega⟩

/-- Input-path bit/current rows returned by the deployed auxiliary allocator. -/
def inputPathRow : Fin 20 → Fin 1024 :=
  ![784, 787, 790, 800, 803, 806, 810, 813, 816, 819,
    822, 825, 828, 831, 834, 837, 840, 843, 846, 849]

/-- Output-path bit/current rows returned by the deployed auxiliary allocator. -/
def outputPathRow : Fin 20 → Fin 1024 :=
  ![785, 788, 791, 801, 804, 807, 811, 814, 817, 820,
    823, 826, 829, 832, 835, 838, 841, 844, 847, 850]

/-- Shared-sibling bit/digest rows returned by the deployed auxiliary allocator. -/
def siblingPathRow : Fin 20 → Fin 1024 :=
  ![786, 789, 798, 802, 805, 808, 812, 815, 818, 821,
    824, 827, 830, 833, 836, 839, 842, 845, 848, 851]

/-- Digest in columns 0 through 7. -/
def lowDigestAt (trace : PhysicalTrace) (row : Fin 1024) : Digest :=
  fun limb => trace row ⟨limb.val, by omega⟩

/-- Digest in columns 1 through 8 (the atomic path auxiliary shape). -/
def pathDigestAt (trace : PhysicalTrace) (row : Fin 1024) : Digest :=
  fun limb => trace row ⟨1 + limb.val, by omega⟩

/-- Digest in columns 2 through 9 (salt source shape). -/
def saltDigestAt (trace : PhysicalTrace) (row : Fin 1024) : Digest :=
  fun limb => trace row ⟨2 + limb.val, by omega⟩

/-- Digest in columns 8 through 15 (key source shape). -/
def highDigestAt (trace : PhysicalTrace) (row : Fin 1024) : Digest :=
  fun limb => trace row ⟨8 + limb.val, by omega⟩

/-- One direct-range witness at its exact three physical rows. -/
def rangeWitnessFromRows
    (trace : PhysicalTrace) (rows : Fin 3 → Fin 1024) : RangeWitness where
  bit := fun limb bit => trace (rows limb) (rangeBitColumn bit)
  limb := fun limb => trace (rows limb) 10
  value := trace (rows 0) 11

/-! ## Maximal unconditional raw projection -/

/--
Every model field that is physically present, without inventing a fee or
collapsing distinct copy-linked cells. Path directions remain field elements
here, because an arbitrary extracted table need not contain Boolean values.
-/
structure RawOpenedColumns where
  rin : RangeWitness
  rout : RangeWitness
  kNu : Digest
  inputSalt : Digest
  outputSalt : Digest
  outputOwnerKey : Digest
  inputOwnerKey : Digest
  inputLeaf : Digest
  nullifier : Digest
  outputCommitment : Digest
  currentAnchor : Digest
  outputAnchor : Digest
  inputAsset : F
  outputAsset : F
  inputPathBits : Fin 20 → F
  outputPathBits : Fin 20 → F
  siblingPathBits : Fin 20 → F
  siblings : Fin 20 → Digest
  /-- Note-hash source alias for the input value. -/
  inputNoteValue : F
  /-- Note-hash source alias for the output value. -/
  outputNoteValue : F
  /-- Balance source alias for the output value. -/
  balanceOutputValue : F

/-- Literal projection of every recoverable opened field and relevant alias. -/
def rawOpenedColumnsFromTrace (trace : PhysicalTrace) : RawOpenedColumns where
  rin := rangeWitnessFromRows trace inputRangeRow
  rout := rangeWitnessFromRows trace outputRangeRow
  kNu := highDigestAt trace 792
  inputSalt := saltDigestAt trace 795
  outputSalt := saltDigestAt trace 799
  outputOwnerKey := highDigestAt trace 796
  inputOwnerKey := lowDigestAt trace 11
  inputLeaf := lowDigestAt trace 59
  nullifier := lowDigestAt trace 731
  outputCommitment := lowDigestAt trace 779
  currentAnchor := lowDigestAt trace 379
  outputAnchor := lowDigestAt trace 699
  inputAsset := trace 795 1
  outputAsset := trace 799 1
  inputPathBits := fun level => trace (inputPathRow level) 0
  outputPathBits := fun level => trace (outputPathRow level) 0
  siblingPathBits := fun level => trace (siblingPathRow level) 0
  siblings := fun level => pathDigestAt trace (siblingPathRow level)
  inputNoteValue := trace 795 0
  outputNoteValue := trace 799 0
  balanceOutputValue := trace 864 12

/-! The range/limb coordinate equalities are definitional, not assumptions. -/

@[simp] theorem raw_rin_bit_cell
    (trace : PhysicalTrace) (limb : Fin 3) (bit : Fin 10) :
    (rawOpenedColumnsFromTrace trace).rin.bit limb bit =
      trace (inputRangeRow limb) (rangeBitColumn bit) := rfl

@[simp] theorem raw_rin_limb_cell
    (trace : PhysicalTrace) (limb : Fin 3) :
    (rawOpenedColumnsFromTrace trace).rin.limb limb =
      trace (inputRangeRow limb) 10 := rfl

@[simp] theorem raw_rin_value_cell (trace : PhysicalTrace) :
    (rawOpenedColumnsFromTrace trace).rin.value = trace 864 11 := rfl

@[simp] theorem raw_rout_bit_cell
    (trace : PhysicalTrace) (limb : Fin 3) (bit : Fin 10) :
    (rawOpenedColumnsFromTrace trace).rout.bit limb bit =
      trace (outputRangeRow limb) (rangeBitColumn bit) := rfl

@[simp] theorem raw_rout_limb_cell
    (trace : PhysicalTrace) (limb : Fin 3) :
    (rawOpenedColumnsFromTrace trace).rout.limb limb =
      trace (outputRangeRow limb) 10 := rfl

@[simp] theorem raw_rout_value_cell (trace : PhysicalTrace) :
    (rawOpenedColumnsFromTrace trace).rout.value = trace 866 11 := rfl

@[simp] theorem raw_input_path_bit_cell
    (trace : PhysicalTrace) (level : Fin 20) :
    (rawOpenedColumnsFromTrace trace).inputPathBits level =
      trace (inputPathRow level) 0 := rfl

@[simp] theorem raw_output_path_bit_cell
    (trace : PhysicalTrace) (level : Fin 20) :
    (rawOpenedColumnsFromTrace trace).outputPathBits level =
      trace (outputPathRow level) 0 := rfl

@[simp] theorem raw_sibling_path_bit_cell
    (trace : PhysicalTrace) (level : Fin 20) :
    (rawOpenedColumnsFromTrace trace).siblingPathBits level =
      trace (siblingPathRow level) 0 := rfl

@[simp] theorem raw_sibling_cell
    (trace : PhysicalTrace) (level : Fin 20) (limb : Fin 8) :
    (rawOpenedColumnsFromTrace trace).siblings level limb =
      trace (siblingPathRow level) ⟨1 + limb.val, by omega⟩ := rfl

/-! ## Exact field-to-Bool boundary -/

/-- Canonical decoder used only with the exactness theorem below. -/
def decodeFieldBit (value : F) : Bool :=
  if value = 1 then true else false

/-- Literal embedding of a Boolean into M31. -/
def boolToField : Bool → F
  | false => 0
  | true => 1

/-- The decoder is exact iff the field element really is Boolean. -/
theorem boolToField_decodeFieldBit_iff (value : F) :
    boolToField (decodeFieldBit value) = value ↔
      value = 0 ∨ value = 1 := by
  by_cases isOne : value = 1
  · subst value
    simp [decodeFieldBit, boolToField]
  · simp [decodeFieldBit, boolToField, isOne, eq_comm]

/-- Concrete (not placeholder) typing condition for the selected path cells. -/
def PathBitsAreBinary (raw : RawOpenedColumns) : Prop :=
  ∀ level, raw.inputPathBits level = 0 ∨ raw.inputPathBits level = 1

/-- The deployed bitness polynomial implies the exact binary typing fact. -/
theorem pathBitsAreBinary_of_bitness
    (raw : RawOpenedColumns)
    (bitness : ∀ level,
      raw.inputPathBits level * (raw.inputPathBits level - 1) = 0) :
    PathBitsAreBinary raw := by
  intro level
  exact field_bool (bitness level)

/-- A concrete input-range cell is binary when its exact bitness equation holds. -/
theorem raw_rin_bit_binary_of_bitness
    (trace : PhysicalTrace) (limb : Fin 3) (bit : Fin 10)
    (bitness :
      trace (inputRangeRow limb) (rangeBitColumn bit) *
        (trace (inputRangeRow limb) (rangeBitColumn bit) - 1) = 0) :
    (rawOpenedColumnsFromTrace trace).rin.bit limb bit = 0 ∨
      (rawOpenedColumnsFromTrace trace).rin.bit limb bit = 1 := by
  change trace (inputRangeRow limb) (rangeBitColumn bit) = 0 ∨
    trace (inputRangeRow limb) (rangeBitColumn bit) = 1
  exact field_bool bitness

/-- A concrete output-range cell is binary when its exact bitness equation holds. -/
theorem raw_rout_bit_binary_of_bitness
    (trace : PhysicalTrace) (limb : Fin 3) (bit : Fin 10)
    (bitness :
      trace (outputRangeRow limb) (rangeBitColumn bit) *
        (trace (outputRangeRow limb) (rangeBitColumn bit) - 1) = 0) :
    (rawOpenedColumnsFromTrace trace).rout.bit limb bit = 0 ∨
      (rawOpenedColumnsFromTrace trace).rout.bit limb bit = 1 := by
  change trace (outputRangeRow limb) (rangeBitColumn bit) = 0 ∨
    trace (outputRangeRow limb) (rangeBitColumn bit) = 1
  exact field_bool bitness

/-! ## All non-fee `OpenedColumns` fields -/

/-- `OpenedColumns` with the public dependent fee pair erased. -/
structure OpenedColumnsExceptFee where
  rin : RangeWitness
  rout : RangeWitness
  kNu : Digest
  inputSalt : Digest
  outputSalt : Digest
  outputOwnerKey : Digest
  inputOwnerKey : Digest
  inputLeaf : Digest
  nullifier : Digest
  outputCommitment : Digest
  currentAnchor : Digest
  outputAnchor : Digest
  inputAsset : F
  outputAsset : F
  bits : Fin 20 → Bool
  siblings : Fin 20 → Digest

/-- Erase exactly `f` and `hf`; no mathematical field is dropped. -/
def eraseFee (opened : OpenedColumns) : OpenedColumnsExceptFee where
  rin := opened.rin
  rout := opened.rout
  kNu := opened.k_nu
  inputSalt := opened.r_in
  outputSalt := opened.r_out
  outputOwnerKey := opened.pk_out
  inputOwnerKey := opened.pk_in
  inputLeaf := opened.L_in
  nullifier := opened.nu
  outputCommitment := opened.C_out
  currentAnchor := opened.A
  outputAnchor := opened.A'
  inputAsset := opened.a_in
  outputAsset := opened.a
  bits := opened.bits
  siblings := opened.sib

/-- Deterministic candidate for every non-fee model field. -/
def decodedOpenedCore (raw : RawOpenedColumns) : OpenedColumnsExceptFee where
  rin := raw.rin
  rout := raw.rout
  kNu := raw.kNu
  inputSalt := raw.inputSalt
  outputSalt := raw.outputSalt
  outputOwnerKey := raw.outputOwnerKey
  inputOwnerKey := raw.inputOwnerKey
  inputLeaf := raw.inputLeaf
  nullifier := raw.nullifier
  outputCommitment := raw.outputCommitment
  currentAnchor := raw.currentAnchor
  outputAnchor := raw.outputAnchor
  inputAsset := raw.inputAsset
  outputAsset := raw.outputAsset
  bits := fun level => decodeFieldBit (raw.inputPathBits level)
  siblings := raw.siblings

/-- The exact public datum absent from C1. -/
structure BoundedFee where
  value : ℕ
  bound : value < 2 ^ 30

/-- Add the statement-supplied bounded fee to a trace-derived core. -/
def completeOpenedColumns
    (core : OpenedColumnsExceptFee) (fee : BoundedFee) : OpenedColumns where
  rin := core.rin
  rout := core.rout
  k_nu := core.kNu
  r_in := core.inputSalt
  r_out := core.outputSalt
  pk_out := core.outputOwnerKey
  pk_in := core.inputOwnerKey
  L_in := core.inputLeaf
  nu := core.nullifier
  C_out := core.outputCommitment
  A := core.currentAnchor
  A' := core.outputAnchor
  a_in := core.inputAsset
  a := core.outputAsset
  bits := core.bits
  sib := core.siblings
  f := fee.value
  hf := fee.bound

/-- Complete candidate from physical trace plus the irreducible public datum. -/
def openedColumnsFromTrace
    (trace : PhysicalTrace) (fee : BoundedFee) : OpenedColumns :=
  completeOpenedColumns (decodedOpenedCore (rawOpenedColumnsFromTrace trace)) fee

@[simp] theorem eraseFee_openedColumnsFromTrace
    (trace : PhysicalTrace) (fee : BoundedFee) :
    eraseFee (openedColumnsFromTrace trace fee) =
      decodedOpenedCore (rawOpenedColumnsFromTrace trace) := rfl

/--
Exact meaning of "the raw trace projects to all non-fee model fields". The
record equality covers every field in `OpenedColumnsExceptFee`; `pathBitExact`
additionally proves that the decoded Bool is the original field cell.
-/
structure RawProjectsToOpenedExceptFee
    (raw : RawOpenedColumns) (opened : OpenedColumns) : Prop where
  core : eraseFee opened = decodedOpenedCore raw
  pathBitExact : ∀ level,
    boolToField (opened.bits level) = raw.inputPathBits level

/-- No unchecked Boolean coercion: exact projection holds iff all path cells are binary. -/
theorem openedColumnsFromTrace_projects_iff_path_bits_binary
    (trace : PhysicalTrace) (fee : BoundedFee) :
    RawProjectsToOpenedExceptFee (rawOpenedColumnsFromTrace trace)
        (openedColumnsFromTrace trace fee) ↔
      PathBitsAreBinary (rawOpenedColumnsFromTrace trace) := by
  constructor
  · intro projects level
    have exact := projects.pathBitExact level
    change boolToField
        (decodeFieldBit
          ((rawOpenedColumnsFromTrace trace).inputPathBits level)) =
        (rawOpenedColumnsFromTrace trace).inputPathBits level at exact
    exact (boolToField_decodeFieldBit_iff _).mp exact
  · intro binary
    refine ⟨rfl, ?_⟩
    intro level
    change boolToField
        (decodeFieldBit
          ((rawOpenedColumnsFromTrace trace).inputPathBits level)) =
        (rawOpenedColumnsFromTrace trace).inputPathBits level
    exact (boolToField_decodeFieldBit_iff _).mpr (binary level)

/-! ## Exact copy-alias target still required from accepted-trace extraction -/

/--
These are the literal equalities that the compiled LogUp source theorem must
produce before one `OpenedColumns` value may stand for every physical use.
This record is a precise target, not evidence manufactured in this file.
-/
structure RequiredTraceAliases (raw : RawOpenedColumns) : Prop where
  inputValue : raw.inputNoteValue = raw.rin.value
  outputValue : raw.outputNoteValue = raw.rout.value
  balanceOutputValue : raw.balanceOutputValue = raw.rout.value
  outputPathBit : ∀ level,
    raw.outputPathBits level = raw.inputPathBits level
  siblingPathBit : ∀ level,
    raw.siblingPathBits level = raw.inputPathBits level

/-! ## The irreducible fee obstruction -/

def boundedFeeZero : BoundedFee := ⟨0, by norm_num⟩
def boundedFeeOne : BoundedFee := ⟨1, by norm_num⟩

/-- The same physical table admits two different bounded-fee completions. -/
theorem trace_does_not_determine_fee (trace : PhysicalTrace) :
    openedColumnsFromTrace trace boundedFeeZero ≠
      openedColumnsFromTrace trace boundedFeeOne := by
  intro equal
  have feeEqual := congrArg (fun opened : OpenedColumns => opened.f) equal
  change 0 = 1 at feeEqual
  omega

/-!
Honesty boundary after this file:

* the statement parser must supply `BoundedFee` (the table cannot);
* accepted semantic extraction must supply `RangeResiduals` for the two exact
  `rin/rout` projections and path-cell bitness;
* accepted compiled-copy extraction must supply `RequiredTraceAliases` and the
  remaining hash/current-value copy identities.

No such residual or copy fact is assumed in any projection theorem above.
-/

#print axioms boolToField_decodeFieldBit_iff
#print axioms pathBitsAreBinary_of_bitness
#print axioms raw_rin_bit_binary_of_bitness
#print axioms raw_rout_bit_binary_of_bitness
#print axioms openedColumnsFromTrace_projects_iff_path_bits_binary
#print axioms trace_does_not_determine_fee

end AspisPool.V7OpenedColumnsFromTrace
