import Mathlib
import AspisFormal.ViewModel

/-!
# Spend opening grammar and released-field inventory

`ViewModel.spendPrefix` checks the arithmetic of a transcribed 6,785-byte v4
prefix.  The current quarantined spend proof does not have a fixed-size suffix.
It appends five private Merkle openings (`C1`, `C2`, `W1`, `W2`, `W3`).  Every
section has the grammar

```text
count_u16_le || (value || salt32)^count || frontier_count_u32_le || frontier32^count
```

and the three later-layer counts can shrink when queried fibres share a
parent.  Consequently, 64,447 bytes is the size of the pinned v4 fixture, not a
protocol-wide proof-length constant.

This file formalises the symbolic length formula, accounts for every released
field payload including the later fold values, and specialises the formula to
the pinned fixture.  Hash roots, salts, Merkle frontier nodes, framing, nonces
and the selector are counted as proof bytes but not as affine field
coordinates.  The Lean results check arithmetic of this source transcription;
they do not parse Rust output or prove source correspondence.  This is a wire
inventory, not a hiding theorem, and it does not assert that any v5 mask covers
these coordinates.
-/

namespace AspisSpendWireView

open AspisViewModel

def openingCountBytes : ℕ := 2
def frontierCountBytes : ℕ := 4
def saltBytes : ℕ := 32
def hashBytes : ℕ := 32
def openingFramingBytes : ℕ := openingCountBytes + frontierCountBytes

def spendQueryCount : ℕ := 18
def c1ValueBytes : ℕ := 416
def c2ValueBytes : ℕ := 192
def laterValueBytes : ℕ := 64

/-- The byte shape of one authenticated private-opening section. -/
structure PrivateOpeningShape where
  /-- Number of distinct opened leaves in this section. -/
  count : ℕ
  /-- Bytes in the field-valued payload of one leaf. -/
  valueBytes : ℕ
  /-- Number of 32-byte hashes in the canonical Merkle frontier. -/
  frontierNodes : ℕ
deriving Repr, DecidableEq

namespace PrivateOpeningShape

def openedValueBytes (s : PrivateOpeningShape) : ℕ := s.count * s.valueBytes
def openedSaltBytes (s : PrivateOpeningShape) : ℕ := s.count * saltBytes
def frontierBytes (s : PrivateOpeningShape) : ℕ := s.frontierNodes * hashBytes

/-- Section length prescribed by the transcribed private-opening grammar. -/
def wireBytes (s : PrivateOpeningShape) : ℕ :=
  openingFramingBytes + s.openedValueBytes + s.openedSaltBytes + s.frontierBytes

theorem wireBytes_decomposition (s : PrivateOpeningShape) :
    s.wireBytes = 6 + s.count * (s.valueBytes + 32) + 32 * s.frontierNodes := by
  simp [wireBytes, openingFramingBytes, openingCountBytes, frontierCountBytes,
    openedValueBytes, openedSaltBytes, frontierBytes, saltBytes, hashBytes]
  ring

end PrivateOpeningShape

/-- The five opening sections in parser order.  The two layer-zero counts are
18 for a production schedule sampled without replacement.  `later1`, `later2`,
and `later3` are the unique counts after shifts by 2, 4, and 6 bits
respectively. -/
def spendSections (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) :
    List PrivateOpeningShape :=
  [ ⟨spendQueryCount, c1ValueBytes, frontierC1⟩,
    ⟨spendQueryCount, c2ValueBytes, frontierC2⟩,
    ⟨later1, laterValueBytes, frontier1⟩,
    ⟨later2, laterValueBytes, frontier2⟩,
    ⟨later3, laterValueBytes, frontier3⟩ ]

theorem spendSections_length
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) :
    (spendSections later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2
      frontier3).length = 5 := by
  rfl

def sumSections (f : PrivateOpeningShape → ℕ)
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) : ℕ :=
  (spendSections later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3).foldr
    (fun item total => f item + total) 0

def frontierTotal (frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) : ℕ :=
  frontierC1 + frontierC2 + frontier1 + frontier2 + frontier3

def laterCountTotal (later1 later2 later3 : ℕ) : ℕ := later1 + later2 + later3

def suffixBytes (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) : ℕ :=
  sumSections PrivateOpeningShape.wireBytes
    later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3

def proofBytes (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) : ℕ :=
  prefixBytes + suffixBytes
    later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3

def openedValueBytes
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) : ℕ :=
  sumSections PrivateOpeningShape.openedValueBytes
    later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3

def openedSaltBytes
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) : ℕ :=
  sumSections PrivateOpeningShape.openedSaltBytes
    later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3

def merkleFrontierBytes
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) : ℕ :=
  sumSections PrivateOpeningShape.frontierBytes
    later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3

def framingBytes
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) : ℕ :=
  sumSections (fun _ => openingFramingBytes)
    later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3

/-- Suffix length for the transcribed grammar, parameterised by the three
derived counts and five frontier sizes. -/
theorem suffixBytes_formula
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) :
    suffixBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 =
      12126 + 96 * laterCountTotal later1 later2 later3
        + 32 * frontierTotal frontierC1 frontierC2 frontier1 frontier2 frontier3 := by
  simp [suffixBytes, sumSections, spendSections, PrivateOpeningShape.wireBytes,
    PrivateOpeningShape.openedValueBytes, PrivateOpeningShape.openedSaltBytes,
    PrivateOpeningShape.frontierBytes, openingFramingBytes, openingCountBytes,
    frontierCountBytes, saltBytes, hashBytes, spendQueryCount, c1ValueBytes,
    c2ValueBytes, laterValueBytes, laterCountTotal, frontierTotal]
  ring

/-- Total proof length in this model.  Only the 6,785-byte prefix is constant. -/
theorem proofBytes_formula
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) :
    proofBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 =
      18911 + 96 * laterCountTotal later1 later2 later3
        + 32 * frontierTotal frontierC1 frontierC2 frontier1 frontier2 frontier3 := by
  rw [proofBytes, suffixBytes_formula]
  norm_num [prefixBytes]
  ring

/-- Opened field payload, excluding salts and authentication hashes. -/
theorem openedValueBytes_formula
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) :
    openedValueBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 =
      10944 + 64 * laterCountTotal later1 later2 later3 := by
  norm_num [openedValueBytes, sumSections, spendSections,
    PrivateOpeningShape.openedValueBytes, spendQueryCount, c1ValueBytes,
    c2ValueBytes, laterValueBytes, laterCountTotal]
  ring

/-- Every opened record releases one 32-byte leaf salt. -/
theorem openedSaltBytes_formula
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) :
    openedSaltBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 =
      1152 + 32 * laterCountTotal later1 later2 later3 := by
  norm_num [openedSaltBytes, sumSections, spendSections,
    PrivateOpeningShape.openedSaltBytes, spendQueryCount, saltBytes, laterCountTotal]
  ring

theorem merkleFrontierBytes_formula
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) :
    merkleFrontierBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 =
      32 * frontierTotal frontierC1 frontierC2 frontier1 frontier2 frontier3 := by
  norm_num [merkleFrontierBytes, sumSections, spendSections,
    PrivateOpeningShape.frontierBytes, hashBytes, frontierTotal]
  ring

/-- Five sections each carry a 2-byte leaf count and 4-byte frontier count. -/
theorem framingBytes_eq
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) :
    framingBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 = 30 := by
  norm_num [framingBytes, sumSections, spendSections, openingFramingBytes,
    openingCountBytes, frontierCountBytes]

/-- The four suffix categories account for every byte in all five sections. -/
theorem suffixBytes_decomposition
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) :
    suffixBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 =
      openedValueBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3
        + openedSaltBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3
        + merkleFrontierBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2
          frontier3
        + framingBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 := by
  rw [suffixBytes_formula, openedValueBytes_formula, openedSaltBytes_formula,
    merkleFrontierBytes_formula, framingBytes_eq]
  ring

/-- The fixed-prefix partition and four suffix categories account for every
proof byte in this model. -/
theorem proofBytes_decomposition
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) :
    proofBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 =
      prefixFieldBytes + prefixNonFieldBytes
        + openedValueBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3
        + openedSaltBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3
        + merkleFrontierBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2
          frontier3
        + framingBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 := by
  rw [proofBytes, suffixBytes_decomposition, ← spendPrefix_counts.2.2.2]
  ring

/-! ## Released field payload

The fixed prefix contains 6,528 field bytes.  `C1` values are canonical M31
words, while `C2` and each later value are canonical QM31 values.  Splitting
QM31 into four M31 coordinates, the M31 coordinate count is one quarter of the
field-payload byte count.  Salts and hashes are not included here.
-/

def releasedFieldBytes
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) : ℕ :=
  prefixFieldBytes + openedValueBytes
    later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3

def releasedM31Coordinates (later1 later2 later3 : ℕ) : ℕ :=
  4368 + 16 * laterCountTotal later1 later2 later3

theorem releasedFieldBytes_formula
    (later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 : ℕ) :
    releasedFieldBytes later1 later2 later3 frontierC1 frontierC2 frontier1 frontier2 frontier3 =
      4 * releasedM31Coordinates later1 later2 later3 := by
  rw [releasedFieldBytes, openedValueBytes_formula]
  have hprefix : prefixFieldBytes = 6528 := spendPrefix_counts.2.1
  rw [hprefix]
  norm_num [releasedM31Coordinates, laterCountTotal]
  ring

/-! ## Necessary bounds on the transcript-derived unique counts

Each later index is the preceding index shifted right by two bits.  Thus a
parent has at most four children: the next count is no larger than the current
count and four times the next count covers the current count.  These conditions
are necessary for counts obtained by those shifts; they are not a complete
characterisation of all index sets.
-/

def ValidDerivedCounts (later1 later2 later3 : ℕ) : Prop :=
  later1 ≤ spendQueryCount ∧ spendQueryCount ≤ 4 * later1 ∧
  later2 ≤ later1 ∧ later1 ≤ 4 * later2 ∧
  later3 ≤ later2 ∧ later2 ≤ 4 * later3

theorem validDerivedCounts_bounds {later1 later2 later3 : ℕ}
    (h : ValidDerivedCounts later1 later2 later3) :
    5 ≤ later1 ∧ later1 ≤ 18 ∧
    2 ≤ later2 ∧ later2 ≤ 18 ∧
    1 ≤ later3 ∧ later3 ≤ 18 := by
  norm_num [ValidDerivedCounts, spendQueryCount] at h ⊢
  omega

theorem releasedM31Coordinates_bounds {later1 later2 later3 : ℕ}
    (h : ValidDerivedCounts later1 later2 later3) :
    4496 ≤ releasedM31Coordinates later1 later2 later3 ∧
      releasedM31Coordinates later1 later2 later3 ≤ 5232 := by
  have hb := validDerivedCounts_bounds h
  simp only [releasedM31Coordinates, laterCountTotal]
  omega

/-! ## Pinned v4 fixture

The Rust byte-inventory regression reports no parent collisions in any of the
three later layers for the committed fixture.  The five recorded frontier sizes
are `317, 317, 263, 209, 155`, totalling 1,261 nodes.  The constants below are a
transcription of those fixture observations; Lean proves the resulting
arithmetic but does not read the binary fixture.
-/

def fixtureLaterCounts : ℕ × ℕ × ℕ := (18, 18, 18)
def fixtureFrontiers : ℕ × ℕ × ℕ × ℕ × ℕ := (317, 317, 263, 209, 155)

theorem fixture_totals :
    laterCountTotal 18 18 18 = 54 ∧
    frontierTotal 317 317 263 209 155 = 1261 := by decide

theorem fixture_section_bytes :
    PrivateOpeningShape.wireBytes ⟨18, 416, 317⟩ = 18214 ∧
    PrivateOpeningShape.wireBytes ⟨18, 192, 317⟩ = 14182 ∧
    PrivateOpeningShape.wireBytes ⟨18, 64, 263⟩ = 10150 ∧
    PrivateOpeningShape.wireBytes ⟨18, 64, 209⟩ = 8422 ∧
    PrivateOpeningShape.wireBytes ⟨18, 64, 155⟩ = 6694 := by
  norm_num [PrivateOpeningShape.wireBytes, PrivateOpeningShape.openedValueBytes,
    PrivateOpeningShape.openedSaltBytes, PrivateOpeningShape.frontierBytes,
    openingFramingBytes, openingCountBytes, frontierCountBytes, saltBytes, hashBytes]

theorem fixture_inventory :
    proofBytes 18 18 18 317 317 263 209 155 = 64447 ∧
    openedValueBytes 18 18 18 317 317 263 209 155 = 14400 ∧
    openedSaltBytes 18 18 18 317 317 263 209 155 = 2880 ∧
    merkleFrontierBytes 18 18 18 317 317 263 209 155 = 40352 ∧
    framingBytes 18 18 18 317 317 263 209 155 = 30 ∧
    releasedM31Coordinates 18 18 18 = 5232 := by
  norm_num [proofBytes_formula, openedValueBytes_formula, openedSaltBytes_formula,
    merkleFrontierBytes_formula, framingBytes_eq, releasedM31Coordinates, laterCountTotal,
    frontierTotal]

end AspisSpendWireView

#print axioms AspisSpendWireView.PrivateOpeningShape.wireBytes_decomposition
#print axioms AspisSpendWireView.spendSections_length
#print axioms AspisSpendWireView.suffixBytes_formula
#print axioms AspisSpendWireView.proofBytes_formula
#print axioms AspisSpendWireView.openedValueBytes_formula
#print axioms AspisSpendWireView.openedSaltBytes_formula
#print axioms AspisSpendWireView.merkleFrontierBytes_formula
#print axioms AspisSpendWireView.framingBytes_eq
#print axioms AspisSpendWireView.suffixBytes_decomposition
#print axioms AspisSpendWireView.proofBytes_decomposition
#print axioms AspisSpendWireView.releasedFieldBytes_formula
#print axioms AspisSpendWireView.validDerivedCounts_bounds
#print axioms AspisSpendWireView.releasedM31Coordinates_bounds
#print axioms AspisSpendWireView.fixture_section_bytes
#print axioms AspisSpendWireView.fixture_inventory
