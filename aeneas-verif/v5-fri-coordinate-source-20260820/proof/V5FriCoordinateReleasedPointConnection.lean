import V5FriCoordinateTopLevel

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 20000000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriCoordinateReleasedPointConnection

open AspisCircleGroupOrder
open AspisV5FriBitReverse
open AspisV5FriCoordinatePointLoops

def fin17U32 (index : Fin (2 ^ 17)) : Std.U32 :=
  ⟨BitVec.ofNat 32 index.val⟩

private theorem reverseBits_eq_bitvecReverse
    (width value : Nat) (hvalue : value < 2 ^ width) :
    reverseBits width value =
      (BitVec.ofNat width value).reverse.toNat := by
  induction width generalizing value with
  | zero =>
      have : value = 0 := by
        norm_num at hvalue
        omega
      subst value
      rfl
  | succ width ih =>
      have htail : value / 2 < 2 ^ width := by
        rw [pow_succ] at hvalue
        omega
      let low : Bool := decide (value % 2 = 1)
      have hdecomp :
          BitVec.ofNat (width + 1) value =
            BitVec.concat (BitVec.ofNat width (value / 2)) low := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvalue,
          BitVec.toNat_concat, Nat.mod_eq_of_lt htail]
        rcases Nat.mod_two_eq_zero_or_one value with hmod | hmod <;>
          simp [low, hmod] <;> omega
      rw [reverseBits, ih (value / 2) htail, hdecomp]
      unfold BitVec.concat
      rw [BitVec.reverse_append]
      simp only [BitVec.reverse_cast, BitVec.toNat_cast,
        BitVec.toNat_append, BitVec.toNat_ofBool]
      have hreverseLow :
          (BitVec.reverse (BitVec.ofBool low)).toNat = low.toNat := by
        cases low <;> decide
      rw [hreverseLow]
      rcases Nat.mod_two_eq_zero_or_one value with hmod | hmod
      · simp [low, hmod]
      · simp only [low, hmod, decide_true, Bool.toNat_true, one_mul]
        have hor := Nat.two_pow_add_eq_or_of_lt
          (b := (BitVec.ofNat width (value / 2)).reverse.toNat)
          (BitVec.reverse (BitVec.ofNat width (value / 2))).isLt 1
        simpa [Nat.add_comm, Nat.one_shiftLeft] using hor

private theorem reverse_shift_setWidth_eq (fiber : Std.U32) (bits : Nat)
    (hbits : 32 ≤ bits) :
    ((BitVec.setWidth bits fiber.bv).reverse >>> (bits - 17)).toNat =
      (BitVec.ofNat 17 fiber.val).reverse.toNat := by
  apply Nat.eq_of_testBit_eq
  intro index
  change
    (((BitVec.setWidth bits fiber.bv).reverse >>> (bits - 17)).getLsbD index) =
      ((BitVec.ofNat 17 fiber.val).reverse.getLsbD index)
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_reverse,
    BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ofNat]
  by_cases hindex : index < 17
  · have houter : bits - 17 + index < bits := by omega
    have hposition :
        bits - 1 - (bits - 17 + index) = 16 - index := by omega
    have hleft : 16 - index < bits := by omega
    have hright : 16 - index < 17 := by omega
    simp only [houter, decide_true, Bool.true_and, hposition,
      hindex, Nat.reduceSubDiff, hleft, hright]
    rfl
  · have hout : ¬ bits - 17 + index < bits := by omega
    simp [hindex, hout]

private theorem sourceNatural_eq_bitvecReverse17 (fiber : Std.U32)
    (_hfiber : fiber.val < 2 ^ 17) :
    (sourceNatural fiber).val =
      (BitVec.ofNat 17 fiber.val).reverse.toNat := by
  rcases System.Platform.numBits_eq with hbits | hbits
  · have hplatform : 32 ≤ System.Platform.numBits := by omega
    have hsource := reverse_shift_setWidth_eq fiber
      System.Platform.numBits hplatform
    have hshift :
        (Std.U32.wrapping_sub core.num.Usize.BITS 17#u32).val %
            System.Platform.numBits = System.Platform.numBits - 17 := by
      norm_num [core.num.Usize.BITS, hbits, Std.U32.wrapping_sub,
        UScalar.wrapping_sub, UScalar.val]
    change
      ((BitVec.setWidth System.Platform.numBits fiber.bv).reverse >>>
          ((Std.U32.wrapping_sub core.num.Usize.BITS 17#u32).val %
            System.Platform.numBits)).toNat =
        (BitVec.ofNat 17 fiber.val).reverse.toNat
    rw [hshift]
    exact hsource
  · have hplatform : 32 ≤ System.Platform.numBits := by omega
    have hsource := reverse_shift_setWidth_eq fiber
      System.Platform.numBits hplatform
    have hshift :
        (Std.U32.wrapping_sub core.num.Usize.BITS 17#u32).val %
            System.Platform.numBits = System.Platform.numBits - 17 := by
      norm_num [core.num.Usize.BITS, hbits, Std.U32.wrapping_sub,
        UScalar.wrapping_sub, UScalar.val]
    change
      ((BitVec.setWidth System.Platform.numBits fiber.bv).reverse >>>
          ((Std.U32.wrapping_sub core.num.Usize.BITS 17#u32).val %
            System.Platform.numBits)).toNat =
        (BitVec.ofNat 17 fiber.val).reverse.toNat
    rw [hshift]
    exact hsource

/-- The machine-word reversal and shift in the translated Rust helper is the
same 17-bit reversal used by the released mathematical domains. -/
theorem sourceNatural_eq_reverseBits17 (fiber : Std.U32)
    (hfiber : fiber.val < 2 ^ 17) :
    (sourceNatural fiber).val = reverseBits 17 fiber.val := by
  calc
    (sourceNatural fiber).val =
        (BitVec.ofNat 17 fiber.val).reverse.toNat :=
      sourceNatural_eq_bitvecReverse17 fiber hfiber
    _ = reverseBits 17 fiber.val :=
      (reverseBits_eq_bitvecReverse 17 fiber.val hfiber).symm

/-- For every in-range stored fibre index, the point selected by the
translated split-window implementation is exactly the released circle point
at that stored index. -/
theorem selectedExpectedPoint_eq_released (fiber : Std.U32)
    (hfiber : fiber.val < 131072) :
    selectedExpectedPoint fiber =
      AspisV5FriInitialCircleEncoderIdentity.storedInitialFibrePoint
        ⟨fiber.val, hfiber⟩ := by
  have hwindow :=
    AspisV5FriCoordinateMathematics.windows_reconstruct_storedInitialFibrePoint
      ⟨fiber.val, hfiber⟩
  rw [AspisV5FriCoordinateMathematics.low_mul_high_eq_representative]
    at hwindow
  simpa [selectedExpectedPoint, reverseFin,
    sourceNatural_eq_reverseBits17 fiber hfiber] using hwindow

def releasedCirclePoint (index : Std.U32) : AspisCircleGroupOrder.C :=
  AspisV5FriInitialCircleEncoderIdentity.storedInitialFibrePoint
    (Fin.ofNat 131072 index.val)

def releasedLine1Point (index : Std.U32) : AspisCircleGroupOrder.C :=
  AspisV5FriReleasedLineGeometry.storedLine17Point
    (AspisV5ComponentCConcreteFoldLinearity.childIndex
      (Fin.ofNat 32768 index.val) 0)

def releasedLine2Point (index : Std.U32) : AspisCircleGroupOrder.C :=
  AspisV5FriReleasedLineGeometry.storedLine15Point
    (AspisV5ComponentCConcreteFoldLinearity.childIndex
      (Fin.ofNat 8192 index.val) 0)

def releasedLine3Point (index : Std.U32) : AspisCircleGroupOrder.C :=
  AspisV5FriReleasedLineGeometry.storedLine13Point
    (AspisV5ComponentCConcreteFoldLinearity.childIndex
      (Fin.ofNat 2048 index.val) 0)

private theorem finOfNat_eq_of_lt (bound value : Nat) [NeZero bound]
    (hvalue : value < bound) :
    Fin.ofNat bound value = ⟨value, hvalue⟩ := by
  apply Fin.ext
  simp [Fin.ofNat, Nat.mod_eq_of_lt hvalue]

theorem selectedExpectedPoint_eq_releasedCirclePoint (fiber : Std.U32)
    (hfiber : fiber.val < 131072) :
    selectedExpectedPoint fiber = releasedCirclePoint fiber := by
  rw [selectedExpectedPoint_eq_released fiber hfiber]
  unfold releasedCirclePoint
  rw [finOfNat_eq_of_lt 131072 fiber.val hfiber]

/-- One-doubling parent generation maps every in-range stored circle child to
the exact released line-1 point named by `child / 4`. -/
theorem circle_parentTransform_eq_releasedLine1
    (child parent : Std.U32)
    (hchild : child.val < 131072)
    (hparent : parent.val < 32768)
    (hmapped : child.val / 4 = parent.val) :
    parentTransform 1#u8 (releasedCirclePoint child) child =
      releasedLine1Point parent := by
  let childFin : Fin 131072 := ⟨child.val, hchild⟩
  let parentFin : Fin 32768 := ⟨parent.val, hparent⟩
  have hchildOfNat : Fin.ofNat 131072 child.val = childFin :=
    finOfNat_eq_of_lt 131072 child.val hchild
  have hparentOfNat : Fin.ofNat 32768 parent.val = parentFin :=
    finOfNat_eq_of_lt 32768 parent.val hparent
  have hparentIndex :
      AspisV5FriConcreteEncoderCommutation.parentIndex (n := 32768)
        childFin = parentFin := by
    apply Fin.ext
    simpa [childFin, parentFin,
      AspisV5FriConcreteEncoderCommutation.parentIndex] using hmapped
  have hslotIndex :
      (⟨child.val % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) =
        AspisV5FriConcreteEncoderCommutation.slotIndex (n := 32768)
          childFin := by
    apply Fin.ext
    simp [childFin, AspisV5FriConcreteEncoderCommutation.slotIndex]
  unfold releasedCirclePoint releasedLine1Point
  rw [hchildOfNat, hparentOfNat]
  unfold parentTransform
  have hone : (1#u8 : Std.U8) ≠ 2#u8 := by decide
  simp only [hone, reduceIte]
  rw [hslotIndex,
    AspisV5FriCoordinateMathematics.circle_child_to_line1_parent childFin,
    hparentIndex]

/-- The first four-fold line step maps an in-range released line-1 child to
the exact released line-2 point named by `child / 4`. -/
theorem line1_parentTransform_eq_releasedLine2
    (child parent : Std.U32)
    (hchild : child.val < 32768)
    (hparent : parent.val < 8192)
    (hmapped : child.val / 4 = parent.val) :
    parentTransform 2#u8 (releasedLine1Point child) child =
      releasedLine2Point parent := by
  let childFin : Fin 32768 := ⟨child.val, hchild⟩
  let parentFin : Fin 8192 := ⟨parent.val, hparent⟩
  have hchildOfNat : Fin.ofNat 32768 child.val = childFin :=
    finOfNat_eq_of_lt 32768 child.val hchild
  have hparentOfNat : Fin.ofNat 8192 parent.val = parentFin :=
    finOfNat_eq_of_lt 8192 parent.val hparent
  have hparentIndex :
      AspisV5FriConcreteEncoderCommutation.parentIndex (n := 8192)
        childFin = parentFin := by
    apply Fin.ext
    simpa [childFin, parentFin,
      AspisV5FriConcreteEncoderCommutation.parentIndex] using hmapped
  have hslotIndex :
      (⟨child.val % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) =
        AspisV5FriConcreteEncoderCommutation.slotIndex (n := 8192)
          childFin := by
    apply Fin.ext
    simp [childFin, AspisV5FriConcreteEncoderCommutation.slotIndex]
  unfold releasedLine1Point releasedLine2Point
  rw [hchildOfNat, hparentOfNat]
  unfold parentTransform
  simp only [reduceIte]
  rw [show
      (AspisV5FriReleasedLineGeometry.storedLine17Point
          (AspisV5ComponentCConcreteFoldLinearity.childIndex childFin 0) ^ 2) ^ 2 =
        AspisV5FriReleasedLineGeometry.storedLine17Point
          (AspisV5ComponentCConcreteFoldLinearity.childIndex childFin 0) ^ 4 by
      rw [← pow_mul]]
  rw [hslotIndex,
    AspisV5FriCoordinateMathematics.line1_child_to_line2_parent childFin,
    hparentIndex]

/-- The second four-fold line step maps an in-range released line-2 child to
the exact released line-3 point named by `child / 4`. -/
theorem line2_parentTransform_eq_releasedLine3
    (child parent : Std.U32)
    (hchild : child.val < 8192)
    (hparent : parent.val < 2048)
    (hmapped : child.val / 4 = parent.val) :
    parentTransform 2#u8 (releasedLine2Point child) child =
      releasedLine3Point parent := by
  let childFin : Fin 8192 := ⟨child.val, hchild⟩
  let parentFin : Fin 2048 := ⟨parent.val, hparent⟩
  have hchildOfNat : Fin.ofNat 8192 child.val = childFin :=
    finOfNat_eq_of_lt 8192 child.val hchild
  have hparentOfNat : Fin.ofNat 2048 parent.val = parentFin :=
    finOfNat_eq_of_lt 2048 parent.val hparent
  have hparentIndex :
      AspisV5FriConcreteEncoderCommutation.parentIndex (n := 2048)
        childFin = parentFin := by
    apply Fin.ext
    simpa [childFin, parentFin,
      AspisV5FriConcreteEncoderCommutation.parentIndex] using hmapped
  have hslotIndex :
      (⟨child.val % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) =
        AspisV5FriConcreteEncoderCommutation.slotIndex (n := 2048)
          childFin := by
    apply Fin.ext
    simp [childFin, AspisV5FriConcreteEncoderCommutation.slotIndex]
  unfold releasedLine2Point releasedLine3Point
  rw [hchildOfNat, hparentOfNat]
  unfold parentTransform
  simp only [reduceIte]
  rw [show
      (AspisV5FriReleasedLineGeometry.storedLine15Point
          (AspisV5ComponentCConcreteFoldLinearity.childIndex childFin 0) ^ 2) ^ 2 =
        AspisV5FriReleasedLineGeometry.storedLine15Point
          (AspisV5ComponentCConcreteFoldLinearity.childIndex childFin 0) ^ 4 by
      rw [← pow_mul]]
  rw [hslotIndex,
    AspisV5FriCoordinateMathematics.line2_child_to_line3_parent childFin,
    hparentIndex]

def IndicesBelow (indices : Slice Std.U32) (bound : Nat) : Prop :=
  ∀ ordinal, ordinal < indices.val.length →
    indices.val[ordinal]!.val < bound

def ReleasedCircleExpected (indices : Slice Std.U32) (ordinal : Nat) :
    AspisCircleGroupOrder.C :=
  releasedCirclePoint indices.val[ordinal]!

def ReleasedLine1Expected (indices : Slice Std.U32) (ordinal : Nat) :
    AspisCircleGroupOrder.C :=
  releasedLine1Point indices.val[ordinal]!

def ReleasedLine2Expected (indices : Slice Std.U32) (ordinal : Nat) :
    AspisCircleGroupOrder.C :=
  releasedLine2Point indices.val[ordinal]!

def ReleasedLine3Expected (indices : Slice Std.U32) (ordinal : Nat) :
    AspisCircleGroupOrder.C :=
  releasedLine3Point indices.val[ordinal]!

theorem circle_parent_expected_compatible
    (layer0 line1 : Slice Std.U32)
    (hlayer0 : IndicesBelow layer0 131072)
    (hline1 : IndicesBelow line1 32768) :
    AspisV5FriCoordinateTopLevel.ParentExpectedCompatible
      layer0 line1 (ReleasedCircleExpected layer0)
        (ReleasedLine1Expected line1) 1#u8 := by
  intro childOrdinal parentOrdinal hchild hparent hmapped
  exact circle_parentTransform_eq_releasedLine1
    layer0.val[childOrdinal]! line1.val[parentOrdinal]!
    (hlayer0 childOrdinal hchild) (hline1 parentOrdinal hparent) hmapped

theorem line1_parent_expected_compatible
    (line1 line2 : Slice Std.U32)
    (hline1 : IndicesBelow line1 32768)
    (hline2 : IndicesBelow line2 8192) :
    AspisV5FriCoordinateTopLevel.ParentExpectedCompatible
      line1 line2 (ReleasedLine1Expected line1)
        (ReleasedLine2Expected line2) 2#u8 := by
  intro childOrdinal parentOrdinal hchild hparent hmapped
  exact line1_parentTransform_eq_releasedLine2
    line1.val[childOrdinal]! line2.val[parentOrdinal]!
    (hline1 childOrdinal hchild) (hline2 parentOrdinal hparent) hmapped

theorem line2_parent_expected_compatible
    (line2 line3 : Slice Std.U32)
    (hline2 : IndicesBelow line2 8192)
    (hline3 : IndicesBelow line3 2048) :
    AspisV5FriCoordinateTopLevel.ParentExpectedCompatible
      line2 line3 (ReleasedLine2Expected line2)
        (ReleasedLine3Expected line3) 2#u8 := by
  intro childOrdinal parentOrdinal hchild hparent hmapped
  exact line2_parentTransform_eq_releasedLine3
    line2.val[childOrdinal]! line3.val[parentOrdinal]!
    (hline2 childOrdinal hchild) (hline3 parentOrdinal hparent) hmapped

theorem selected_points_represent_released
    (layer0 : Slice Std.U32)
    (points : AspisV5FriCoordinateTopLevel.Coordinate.PointVec)
    (hlayer0 : IndicesBelow layer0 131072)
    (hpost : SelectedPointsPost layer0 points) :
    points.val.length = layer0.val.length ∧
      ∀ ordinal, ordinal < points.val.length →
        Represents points.val[ordinal]!
          (ReleasedCircleExpected layer0 ordinal) := by
  refine ⟨hpost.1, ?_⟩
  intro ordinal hordinal
  have hlayerOrdinal : ordinal < layer0.val.length := by
    simpa [hpost.1] using hordinal
  have hmeaning := hpost.2 ordinal hlayerOrdinal
  rw [selectedExpectedPoint_eq_releasedCirclePoint
    layer0.val[ordinal]! (hlayer0 ordinal hlayerOrdinal)] at hmeaning
  exact hmeaning

structure ReleasedPointListsEvidence
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points :
      AspisV5FriCoordinateTopLevel.Coordinate.PointVec) : Prop where
  circleLength : circlePoints.val.length = layer0.val.length
  line1Length : line1Points.val.length = line1.val.length
  line2Length : line2Points.val.length = line2.val.length
  line3Length : line3Points.val.length = line3.val.length
  circle : ∀ ordinal, ordinal < circlePoints.val.length →
    Represents circlePoints.val[ordinal]!
      (ReleasedCircleExpected layer0 ordinal)
  line1 : ∀ ordinal, ordinal < line1Points.val.length →
    Represents line1Points.val[ordinal]!
      (ReleasedLine1Expected line1 ordinal)
  line2 : ∀ ordinal, ordinal < line2Points.val.length →
    Represents line2Points.val[ordinal]!
      (ReleasedLine2Expected line2 ordinal)
  line3 : ∀ ordinal, ordinal < line3Points.val.length →
    Represents line3Points.val[ordinal]!
      (ReleasedLine3Expected line3 ordinal)

/-- Successful translated point-helper calls over in-range release indices
return exactly the four released point lists. -/
theorem accepted_point_helpers_represent_released
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points :
      AspisV5FriCoordinateTopLevel.Coordinate.PointVec)
    (hlayer0 : IndicesBelow layer0 131072)
    (hline1 : IndicesBelow line1 32768)
    (hline2 : IndicesBelow line2 8192)
    (hline3 : IndicesBelow line3 2048)
    (hcircleCall :
      V5FriCoordinateAdapter.aspis_core.circle_fri.selected_circle_fiber_points_shared
          19#u32 layer0 = .ok (circlePoints, true))
    (hline1Call :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          layer0 (alloc.vec.Vec.deref circlePoints) line1 1#u8 =
        .ok (line1Points, true))
    (hline2Call :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          line1 (alloc.vec.Vec.deref line1Points) line2 2#u8 =
        .ok (line2Points, true))
    (hline3Call :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          line2 (alloc.vec.Vec.deref line2Points) line3 2#u8 =
        .ok (line3Points, true)) :
    ReleasedPointListsEvidence layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points := by
  have hcirclePost := selected_circle_fiber_points_shared_success
    19#u32 layer0 circlePoints true hcircleCall
  have hcircle := selected_points_represent_released layer0 circlePoints
    hlayer0 hcirclePost
  have hline1Meaning :=
    AspisV5FriCoordinateTopLevel.parent_success_exact_expected
      layer0 (alloc.vec.Vec.deref circlePoints) line1 1#u8
      (ReleasedCircleExpected layer0) (ReleasedLine1Expected line1)
      line1Points hcircle.2
      (circle_parent_expected_compatible layer0 line1 hlayer0 hline1)
      hline1Call
  have hline2Meaning :=
    AspisV5FriCoordinateTopLevel.parent_success_exact_expected
      line1 (alloc.vec.Vec.deref line1Points) line2 2#u8
      (ReleasedLine1Expected line1) (ReleasedLine2Expected line2)
      line2Points hline1Meaning.2
      (line1_parent_expected_compatible line1 line2 hline1 hline2)
      hline2Call
  have hline3Meaning :=
    AspisV5FriCoordinateTopLevel.parent_success_exact_expected
      line2 (alloc.vec.Vec.deref line2Points) line3 2#u8
      (ReleasedLine2Expected line2) (ReleasedLine3Expected line3)
      line3Points hline2Meaning.2
      (line2_parent_expected_compatible line2 line3 hline2 hline3)
      hline3Call
  exact
    { circleLength := hcircle.1
      line1Length := hline1Meaning.1
      line2Length := hline2Meaning.1
      line3Length := hline3Meaning.1
      circle := hcircle.2
      line1 := hline1Meaning.2
      line2 := hline2Meaning.2
      line3 := hline3Meaning.2 }

private theorem releasedCirclePoint_nonzero_fin (index : Fin 131072) :
    2 * (AspisV5FriInitialCircleEncoderIdentity.storedInitialFibrePoint
          index).1.1 ≠ 0 ∧
      2 * (AspisV5FriInitialCircleEncoderIdentity.storedInitialFibrePoint
          index).1.2 ≠ 0 := by
  constructor
  · apply mul_ne_zero AspisCircleGroupOrder.two_ne_zero_ZModP
    simpa [AspisV5FriReleasedLineGeometry.releasedEvaluationPoints,
      AspisV5FriReleasedLineGeometry.releasedLinePoints,
      AspisCircleGroupOrder.X] using
        AspisV5AcceptedExecutionReleasedSchedule.released_circle_x_ne_zero index
  · apply mul_ne_zero AspisCircleGroupOrder.two_ne_zero_ZModP
    simpa [AspisV5FriReleasedLineGeometry.releasedEvaluationPoints,
      AspisV5FriReleasedLineGeometry.releasedLinePoints] using
        AspisV5AcceptedExecutionReleasedSchedule.released_circle_y_ne_zero index

private theorem releasedLine1Point_nonzero_fin (index : Fin 32768) :
    let point := AspisV5FriReleasedLineGeometry.storedLine17Point
      (AspisV5ComponentCConcreteFoldLinearity.childIndex index 0)
    2 * point.1.1 ≠ 0 ∧ 2 * point.1.2 ≠ 0 ∧
      2 * (2 * point.1.1 ^ 2 - 1) ≠ 0 := by
  dsimp only
  have hx : AspisV5FriReleasedLineGeometry.storedLine17X
      (AspisV5ComponentCConcreteFoldLinearity.childIndex index 0) ≠ 0 := by
    have h :=
      AspisV5AcceptedExecutionReleasedSchedule.released_line1_ne_zero index 0
    simpa [AspisV5FriReleasedLineGeometry.releasedEvaluationPoints,
      AspisV5FriReleasedLineGeometry.releasedLinePoints,
      AspisV5ComponentCConcreteFoldLinearity.layer2Symbols] using h
  have hy :
      (AspisV5FriReleasedLineGeometry.storedLine17Point
        (AspisV5ComponentCConcreteFoldLinearity.childIndex index 0)).1.2 ≠ 0 := by
    have h :=
      AspisV5AcceptedExecutionReleasedSchedule.released_line1_ne_zero index 1
    rw [AspisV5FriCoordinateMathematics.storedLine17_slot0_y_eq_slot2_x
      index]
    simpa [AspisV5FriReleasedLineGeometry.releasedEvaluationPoints,
      AspisV5FriReleasedLineGeometry.releasedLinePoints,
      AspisV5ComponentCConcreteFoldLinearity.layer2Symbols] using h
  have ht2 : AspisCircleTensorBinding.doubledFactor
      (AspisV5FriReleasedLineGeometry.storedLine17X
        (AspisV5ComponentCConcreteFoldLinearity.childIndex index 0)) 1 ≠ 0 := by
    have h :=
      AspisV5AcceptedExecutionReleasedSchedule.released_line1_ne_zero index 2
    rw [AspisV5FriReleasedLineGeometry.storedLine17_t2_slot0]
    simpa [AspisV5FriReleasedLineGeometry.releasedEvaluationPoints,
      AspisV5FriReleasedLineGeometry.releasedLinePoints,
      AspisV5ComponentCConcreteFoldLinearity.layer2Symbols] using h
  exact ⟨mul_ne_zero AspisCircleGroupOrder.two_ne_zero_ZModP
      (by simpa [AspisV5FriReleasedLineGeometry.storedLine17X,
        AspisCircleGroupOrder.X] using hx),
    mul_ne_zero AspisCircleGroupOrder.two_ne_zero_ZModP hy,
    mul_ne_zero AspisCircleGroupOrder.two_ne_zero_ZModP
      (by simpa [AspisCircleTensorBinding.doubledFactor,
        AspisV5FriReleasedLineGeometry.storedLine17X,
        AspisCircleGroupOrder.X] using ht2)⟩

private theorem releasedLine2Point_nonzero_fin (index : Fin 8192) :
    let point := AspisV5FriReleasedLineGeometry.storedLine15Point
      (AspisV5ComponentCConcreteFoldLinearity.childIndex index 0)
    2 * point.1.1 ≠ 0 ∧ 2 * point.1.2 ≠ 0 ∧
      2 * (2 * point.1.1 ^ 2 - 1) ≠ 0 := by
  dsimp only
  have hx : AspisV5FriReleasedLineGeometry.storedLine15X
      (AspisV5ComponentCConcreteFoldLinearity.childIndex index 0) ≠ 0 := by
    have h :=
      AspisV5AcceptedExecutionReleasedSchedule.released_line2_ne_zero index 0
    simpa [AspisV5FriReleasedLineGeometry.releasedEvaluationPoints,
      AspisV5FriReleasedLineGeometry.releasedLinePoints,
      AspisV5ComponentCConcreteFoldLinearity.layer3Symbols] using h
  have hy :
      (AspisV5FriReleasedLineGeometry.storedLine15Point
        (AspisV5ComponentCConcreteFoldLinearity.childIndex index 0)).1.2 ≠ 0 := by
    have h :=
      AspisV5AcceptedExecutionReleasedSchedule.released_line2_ne_zero index 1
    rw [AspisV5FriCoordinateMathematics.storedLine15_slot0_y_eq_slot2_x
      index]
    simpa [AspisV5FriReleasedLineGeometry.releasedEvaluationPoints,
      AspisV5FriReleasedLineGeometry.releasedLinePoints,
      AspisV5ComponentCConcreteFoldLinearity.layer3Symbols] using h
  have ht2 : AspisCircleTensorBinding.doubledFactor
      (AspisV5FriReleasedLineGeometry.storedLine15X
        (AspisV5ComponentCConcreteFoldLinearity.childIndex index 0)) 1 ≠ 0 := by
    have h :=
      AspisV5AcceptedExecutionReleasedSchedule.released_line2_ne_zero index 2
    rw [AspisV5FriReleasedLineGeometry.storedLine15_t2_slot0]
    simpa [AspisV5FriReleasedLineGeometry.releasedEvaluationPoints,
      AspisV5FriReleasedLineGeometry.releasedLinePoints,
      AspisV5ComponentCConcreteFoldLinearity.layer3Symbols] using h
  exact ⟨mul_ne_zero AspisCircleGroupOrder.two_ne_zero_ZModP
      (by simpa [AspisV5FriReleasedLineGeometry.storedLine15X,
        AspisCircleGroupOrder.X] using hx),
    mul_ne_zero AspisCircleGroupOrder.two_ne_zero_ZModP hy,
    mul_ne_zero AspisCircleGroupOrder.two_ne_zero_ZModP
      (by simpa [AspisCircleTensorBinding.doubledFactor,
        AspisV5FriReleasedLineGeometry.storedLine15X,
        AspisCircleGroupOrder.X] using ht2)⟩

private theorem releasedLine3Point_nonzero_fin (index : Fin 2048) :
    let point := AspisV5FriReleasedLineGeometry.storedLine13Point
      (AspisV5ComponentCConcreteFoldLinearity.childIndex index 0)
    2 * point.1.1 ≠ 0 ∧ 2 * point.1.2 ≠ 0 ∧
      2 * (2 * point.1.1 ^ 2 - 1) ≠ 0 := by
  dsimp only
  have hx : AspisV5FriReleasedLineGeometry.storedLine13X
      (AspisV5ComponentCConcreteFoldLinearity.childIndex index 0) ≠ 0 := by
    have h :=
      AspisV5AcceptedExecutionReleasedSchedule.released_line3_ne_zero index 0
    simpa [AspisV5FriReleasedLineGeometry.releasedEvaluationPoints,
      AspisV5FriReleasedLineGeometry.releasedLinePoints,
      AspisV5ComponentCConcreteFoldLinearity.layer4Symbols] using h
  have hy :
      (AspisV5FriReleasedLineGeometry.storedLine13Point
        (AspisV5ComponentCConcreteFoldLinearity.childIndex index 0)).1.2 ≠ 0 := by
    have h :=
      AspisV5AcceptedExecutionReleasedSchedule.released_line3_ne_zero index 1
    rw [AspisV5FriCoordinateMathematics.storedLine13_slot0_y_eq_slot2_x
      index]
    simpa [AspisV5FriReleasedLineGeometry.releasedEvaluationPoints,
      AspisV5FriReleasedLineGeometry.releasedLinePoints,
      AspisV5ComponentCConcreteFoldLinearity.layer4Symbols] using h
  have ht2 : AspisCircleTensorBinding.doubledFactor
      (AspisV5FriReleasedLineGeometry.storedLine13X
        (AspisV5ComponentCConcreteFoldLinearity.childIndex index 0)) 1 ≠ 0 := by
    have h :=
      AspisV5AcceptedExecutionReleasedSchedule.released_line3_ne_zero index 2
    rw [AspisV5FriReleasedLineGeometry.storedLine13_t2_slot0]
    simpa [AspisV5FriReleasedLineGeometry.releasedEvaluationPoints,
      AspisV5FriReleasedLineGeometry.releasedLinePoints,
      AspisV5ComponentCConcreteFoldLinearity.layer4Symbols] using h
  exact ⟨mul_ne_zero AspisCircleGroupOrder.two_ne_zero_ZModP
      (by simpa [AspisV5FriReleasedLineGeometry.storedLine13X,
        AspisCircleGroupOrder.X] using hx),
    mul_ne_zero AspisCircleGroupOrder.two_ne_zero_ZModP hy,
    mul_ne_zero AspisCircleGroupOrder.two_ne_zero_ZModP
      (by simpa [AspisCircleTensorBinding.doubledFactor,
        AspisV5FriReleasedLineGeometry.storedLine13X,
        AspisCircleGroupOrder.X] using ht2)⟩

/-- Every released initial-circle point selected by an in-range source index
has the two nonzero denominators used by the production coordinate helper. -/
theorem releasedCircleExpected_nonzero
    (indices : Slice Std.U32) (hindices : IndicesBelow indices 131072) :
    ∀ ordinal, ordinal < indices.val.length →
      2 * (ReleasedCircleExpected indices ordinal).1.1 ≠ 0 ∧
      2 * (ReleasedCircleExpected indices ordinal).1.2 ≠ 0 := by
  intro ordinal hord
  have hindex := hindices ordinal hord
  unfold ReleasedCircleExpected releasedCirclePoint
  rw [finOfNat_eq_of_lt 131072 indices.val[ordinal]!.val hindex]
  exact releasedCirclePoint_nonzero_fin
    ⟨indices.val[ordinal]!.val, hindex⟩

/-- Every released first-line point selected by an in-range source index has
the three nonzero denominators used by the production coordinate helper. -/
theorem releasedLine1Expected_nonzero
    (indices : Slice Std.U32) (hindices : IndicesBelow indices 32768) :
    ∀ ordinal, ordinal < indices.val.length →
      2 * (ReleasedLine1Expected indices ordinal).1.1 ≠ 0 ∧
      2 * (ReleasedLine1Expected indices ordinal).1.2 ≠ 0 ∧
      2 * (2 * (ReleasedLine1Expected indices ordinal).1.1 ^ 2 - 1) ≠ 0 := by
  intro ordinal hord
  have hindex := hindices ordinal hord
  unfold ReleasedLine1Expected releasedLine1Point
  rw [finOfNat_eq_of_lt 32768 indices.val[ordinal]!.val hindex]
  exact releasedLine1Point_nonzero_fin
    ⟨indices.val[ordinal]!.val, hindex⟩

/-- Every released second-line point selected by an in-range source index has
the three nonzero denominators used by the production coordinate helper. -/
theorem releasedLine2Expected_nonzero
    (indices : Slice Std.U32) (hindices : IndicesBelow indices 8192) :
    ∀ ordinal, ordinal < indices.val.length →
      2 * (ReleasedLine2Expected indices ordinal).1.1 ≠ 0 ∧
      2 * (ReleasedLine2Expected indices ordinal).1.2 ≠ 0 ∧
      2 * (2 * (ReleasedLine2Expected indices ordinal).1.1 ^ 2 - 1) ≠ 0 := by
  intro ordinal hord
  have hindex := hindices ordinal hord
  unfold ReleasedLine2Expected releasedLine2Point
  rw [finOfNat_eq_of_lt 8192 indices.val[ordinal]!.val hindex]
  exact releasedLine2Point_nonzero_fin
    ⟨indices.val[ordinal]!.val, hindex⟩

/-- Every released third-line point selected by an in-range source index has
the three nonzero denominators used by the production coordinate helper. -/
theorem releasedLine3Expected_nonzero
    (indices : Slice Std.U32) (hindices : IndicesBelow indices 2048) :
    ∀ ordinal, ordinal < indices.val.length →
      2 * (ReleasedLine3Expected indices ordinal).1.1 ≠ 0 ∧
      2 * (ReleasedLine3Expected indices ordinal).1.2 ≠ 0 ∧
      2 * (2 * (ReleasedLine3Expected indices ordinal).1.1 ^ 2 - 1) ≠ 0 := by
  intro ordinal hord
  have hindex := hindices ordinal hord
  unfold ReleasedLine3Expected releasedLine3Point
  rw [finOfNat_eq_of_lt 2048 indices.val[ordinal]!.val hindex]
  exact releasedLine3Point_nonzero_fin
    ⟨indices.val[ordinal]!.val, hindex⟩

/-- For in-range released index lists, the accepted translated point-helper
calls are sufficient to run the complete translated coordinate adapter.  Its
flat vector contains the exact inverses of the exact released denominators,
and its output uses the production layout. -/
theorem extracted_released_coordinate_path_exact
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points :
      AspisV5FriCoordinateTopLevel.Coordinate.PointVec)
    (hlayer0 : IndicesBelow layer0 131072)
    (hline1 : IndicesBelow line1 32768)
    (hline2 : IndicesBelow line2 8192)
    (hline3 : IndicesBelow line3 2048)
    (hcircleCall :
      V5FriCoordinateAdapter.aspis_core.circle_fri.selected_circle_fiber_points_shared
          19#u32 layer0 = .ok (circlePoints, true))
    (hline1Call :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          layer0 (alloc.vec.Vec.deref circlePoints) line1 1#u8 =
        .ok (line1Points, true))
    (hline2Call :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          line1 (alloc.vec.Vec.deref line1Points) line2 2#u8 =
        .ok (line2Points, true))
    (hline3Call :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          line2 (alloc.vec.Vec.deref line2Points) line3 2#u8 =
        .ok (line3Points, true))
    (hcircleNonempty : 0 < layer0.val.length)
    (hcapacity : 2 * layer0.val.length +
        3 * (line1.val.length + line2.val.length + line3.val.length) ≤
          Std.Usize.max) :
    ∃ circleDenominators denominators flat output,
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle
          19#u32 layer0 line1 line2 line3 = .ok (.Ok output) ∧
      AspisV5FriCoordinateDenominatorLoops.CirclePost circlePoints
        (circleDenominators, none) ∧
      AspisV5FriCoordinateDenominatorLoops.ThreeLineLayerPost
        circleDenominators line1Points line2Points line3Points
        (denominators, none) ∧
      AspisV5FriCoordinateInverseLoops.BatchInverseEvidence denominators flat ∧
      AspisV5FriCoordinateOutputLoops.AcceptedOutputEvidence
        layer0 line1 line2 line3 flat line3Points output := by
  have evidence := accepted_point_helpers_represent_released
    layer0 line1 line2 line3 circlePoints line1Points line2Points line3Points
    hlayer0 hline1 hline2 hline3 hcircleCall hline1Call hline2Call hline3Call
  have hcircleCanonical :=
    AspisV5FriCoordinateTopLevel.canonicalPoints_of_represents
      circlePoints (ReleasedCircleExpected layer0) evidence.circle
  have hline1Canonical :=
    AspisV5FriCoordinateTopLevel.canonicalPoints_of_represents
      line1Points (ReleasedLine1Expected line1) evidence.line1
  have hline2Canonical :=
    AspisV5FriCoordinateTopLevel.canonicalPoints_of_represents
      line2Points (ReleasedLine2Expected line2) evidence.line2
  have hline3Canonical :=
    AspisV5FriCoordinateTopLevel.canonicalPoints_of_represents
      line3Points (ReleasedLine3Expected line3) evidence.line3
  have hcircleNonzero :=
    AspisV5FriCoordinateTopLevel.circle_nonzero_of_represents
      circlePoints (ReleasedCircleExpected layer0) evidence.circle
      (fun index hindex => releasedCircleExpected_nonzero layer0 hlayer0
        index (by simpa [evidence.circleLength] using hindex))
  have hline1Nonzero :=
    AspisV5FriCoordinateTopLevel.line_nonzero_of_represents
      line1Points (ReleasedLine1Expected line1) evidence.line1
      (fun index hindex => releasedLine1Expected_nonzero line1 hline1
        index (by simpa [evidence.line1Length] using hindex))
  have hline2Nonzero :=
    AspisV5FriCoordinateTopLevel.line_nonzero_of_represents
      line2Points (ReleasedLine2Expected line2) evidence.line2
      (fun index hindex => releasedLine2Expected_nonzero line2 hline2
        index (by simpa [evidence.line2Length] using hindex))
  have hline3Nonzero :=
    AspisV5FriCoordinateTopLevel.line_nonzero_of_represents
      line3Points (ReleasedLine3Expected line3) evidence.line3
      (fun index hindex => releasedLine3Expected_nonzero line3 hline3
        index (by simpa [evidence.line3Length] using hindex))
  apply AspisV5FriCoordinateTopLevel.extracted_accepted_path_exact
    layer0 line1 line2 line3 circlePoints line1Points line2Points line3Points
    hcircleCall hline1Call hline2Call hline3Call
    evidence.circleLength evidence.line1Length evidence.line2Length
    evidence.line3Length hcircleCanonical hline1Canonical hline2Canonical
    hline3Canonical
  · simpa [evidence.circleLength] using hcircleNonempty
  · simpa [evidence.circleLength, evidence.line1Length,
      evidence.line2Length, evidence.line3Length] using hcapacity
  · exact hcircleNonzero
  · exact hline1Nonzero
  · exact hline2Nonzero
  · exact hline3Nonzero

/-- The two output coordinates for each initial-circle query are the exact
inverses of the two released mathematical denominators. -/
theorem accepted_output_circle_exact
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points :
      AspisV5FriCoordinateTopLevel.Coordinate.PointVec)
    (circleDenominators denominators flat :
      AspisV5FriCoordinateTopLevel.Coordinate.M31Vec)
    (output : AspisV5FriCoordinateTopLevel.Coordinate.Output)
    (hpoints : ReleasedPointListsEvidence layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points)
    (hcircle : AspisV5FriCoordinateDenominatorLoops.CirclePost circlePoints
      (circleDenominators, none))
    (hinverses : AspisV5FriCoordinateInverseLoops.BatchInverseEvidence
      denominators flat)
    (hdenominatorLength : circleDenominators.val.length ≤
      denominators.val.length)
    (hdenominatorPrefix : ∀ index, index < circleDenominators.val.length →
      denominators.val[index]! = circleDenominators.val[index]!)
    (houtput : AspisV5FriCoordinateOutputLoops.AcceptedOutputEvidence
      layer0 line1 line2 line3 flat line3Points output) :
    ∀ ordinal, ordinal < layer0.val.length →
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.circle.val[ordinal]!.val[0]! =
        (2 * (ReleasedCircleExpected layer0 ordinal).1.1)⁻¹ ∧
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.circle.val[ordinal]!.val[1]! =
        (2 * (ReleasedCircleExpected layer0 ordinal).1.2)⁻¹ := by
  intro ordinal hord
  rcases hcircle with ⟨hcircleLength, _hcanonical, _hzero, hcircleValues⟩
  rcases hinverses with ⟨hflatLength, _hflatCanonical, hflatValues⟩
  have hpointBound : ordinal < circlePoints.val.length := by
    simpa [hpoints.circleLength] using hord
  have hcircleSlot0 : 2 * ordinal < circleDenominators.val.length := by
    rw [hcircleLength]
    omega
  have hcircleSlot1 : 2 * ordinal + 1 < circleDenominators.val.length := by
    rw [hcircleLength]
    omega
  have hdenominatorSlot0 : 2 * ordinal < denominators.val.length := by
    omega
  have hdenominatorSlot1 : 2 * ordinal + 1 < denominators.val.length := by
    omega
  have houtput0 : output.circle.val[ordinal]!.val[0]! =
      flat.val[2 * ordinal]! := by
    rw [houtput.1,
      AspisV5FriCoordinateOutputLoops.pairOutput_get_zero flat 0
        layer0.val.length ordinal hord]
    simp
  have houtput1 : output.circle.val[ordinal]!.val[1]! =
      flat.val[2 * ordinal + 1]! := by
    rw [houtput.1,
      AspisV5FriCoordinateOutputLoops.pairOutput_get_one flat 0
        layer0.val.length ordinal hord]
    simp
  have hmeaning := hpoints.circle ordinal hpointBound
  have hx : AspisV5FriCoordinateFieldSemantics.m31Value
      circlePoints.val[ordinal]!.x =
        (ReleasedCircleExpected layer0 ordinal).1.1 :=
    congrArg Prod.fst hmeaning.2
  have hy : AspisV5FriCoordinateFieldSemantics.m31Value
      circlePoints.val[ordinal]!.y =
        (ReleasedCircleExpected layer0 ordinal).1.2 :=
    congrArg Prod.snd hmeaning.2
  constructor
  · rw [houtput0, hflatValues (2 * ordinal) hdenominatorSlot0,
      hdenominatorPrefix (2 * ordinal) hcircleSlot0,
      (hcircleValues ordinal hpointBound).1, hx]
  · rw [houtput1, hflatValues (2 * ordinal + 1) hdenominatorSlot1,
      hdenominatorPrefix (2 * ordinal + 1) hcircleSlot1,
      (hcircleValues ordinal hpointBound).2, hy]

/-- The three first-line output coordinates for each query are the exact
inverses of the released point's `2*x`, `2*y`, and `2*(2*x^2-1)`. -/
theorem accepted_output_line1_exact
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points :
      AspisV5FriCoordinateTopLevel.Coordinate.PointVec)
    (circleDenominators denominators flat :
      AspisV5FriCoordinateTopLevel.Coordinate.M31Vec)
    (output : AspisV5FriCoordinateTopLevel.Coordinate.Output)
    (hpoints : ReleasedPointListsEvidence layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points)
    (hcircle : AspisV5FriCoordinateDenominatorLoops.CirclePost circlePoints
      (circleDenominators, none))
    (hlines : AspisV5FriCoordinateDenominatorLoops.ThreeLineLayerPost
      circleDenominators line1Points line2Points line3Points
      (denominators, none))
    (hinverses : AspisV5FriCoordinateInverseLoops.BatchInverseEvidence
      denominators flat)
    (houtput : AspisV5FriCoordinateOutputLoops.AcceptedOutputEvidence
      layer0 line1 line2 line3 flat line3Points output) :
    ∀ ordinal, ordinal < line1.val.length →
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.later.val[0]!.val[ordinal]!.val[0]! =
        (2 * (ReleasedLine1Expected line1 ordinal).1.1)⁻¹ ∧
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.later.val[0]!.val[ordinal]!.val[1]! =
        (2 * (ReleasedLine1Expected line1 ordinal).1.2)⁻¹ ∧
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.later.val[0]!.val[ordinal]!.val[2]! =
        (2 * (2 * (ReleasedLine1Expected line1 ordinal).1.1 ^ 2 - 1))⁻¹ := by
  intro ordinal hord
  rcases hcircle with ⟨hcircleLength, _hcircleCanonical, _hzero,
    _hcircleValues⟩
  have hlineValues :=
    AspisV5FriCoordinateDenominatorLoops.threeLineLayerPost_exact_values
      circleDenominators denominators line1Points line2Points line3Points
      hlines
  rcases hlineValues with
    ⟨hdenominatorLength, _hprefix, hline1Values, _hline2Values,
      _hline3Values⟩
  rcases hinverses with ⟨_hflatLength, _hflatCanonical, hflatValues⟩
  rcases houtput with ⟨_hcircleOutput, later0, later1, later2,
    hlater, hlater0, _hlater1, _hlater2, _hfinal⟩
  have hpointBound : ordinal < line1Points.val.length := by
    simpa [hpoints.line1Length] using hord
  have hcircleOffset : circleDenominators.val.length =
      2 * layer0.val.length := by
    rw [hcircleLength, hpoints.circleLength]
  have hslot0 : circleDenominators.val.length + 3 * ordinal <
      denominators.val.length := by omega
  have hslot1 : circleDenominators.val.length + 3 * ordinal + 1 <
      denominators.val.length := by omega
  have hslot2 : circleDenominators.val.length + 3 * ordinal + 2 <
      denominators.val.length := by omega
  have houtput0 : output.later.val[0]!.val[ordinal]!.val[0]! =
      flat.val[circleDenominators.val.length + 3 * ordinal]! := by
    rw [hlater]
    change later0.val[ordinal]!.val[0]! = _
    rw [hlater0,
      AspisV5FriCoordinateOutputLoops.tripleOutput_get_zero flat
        (2 * layer0.val.length) line1.val.length ordinal hord,
      ← hcircleOffset]
  have houtput1 : output.later.val[0]!.val[ordinal]!.val[1]! =
      flat.val[circleDenominators.val.length + 3 * ordinal + 1]! := by
    rw [hlater]
    change later0.val[ordinal]!.val[1]! = _
    rw [hlater0,
      AspisV5FriCoordinateOutputLoops.tripleOutput_get_one flat
        (2 * layer0.val.length) line1.val.length ordinal hord,
      ← hcircleOffset]
  have houtput2 : output.later.val[0]!.val[ordinal]!.val[2]! =
      flat.val[circleDenominators.val.length + 3 * ordinal + 2]! := by
    rw [hlater]
    change later0.val[ordinal]!.val[2]! = _
    rw [hlater0,
      AspisV5FriCoordinateOutputLoops.tripleOutput_get_two flat
        (2 * layer0.val.length) line1.val.length ordinal hord,
      ← hcircleOffset]
  have hmeaning := hpoints.line1 ordinal hpointBound
  have hx : AspisV5FriCoordinateFieldSemantics.m31Value
      line1Points.val[ordinal]!.x =
        (ReleasedLine1Expected line1 ordinal).1.1 :=
    congrArg Prod.fst hmeaning.2
  have hy : AspisV5FriCoordinateFieldSemantics.m31Value
      line1Points.val[ordinal]!.y =
        (ReleasedLine1Expected line1 ordinal).1.2 :=
    congrArg Prod.snd hmeaning.2
  have hvalues := hline1Values ordinal hpointBound
  constructor
  · rw [houtput0, hflatValues _ hslot0, hvalues.1, hx]
  · constructor
    · rw [houtput1, hflatValues _ hslot1, hvalues.2.1, hy]
    · rw [houtput2, hflatValues _ hslot2, hvalues.2.2, hx]

/-- Exact released inverse coordinates for the second line layer. -/
theorem accepted_output_line2_exact
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points :
      AspisV5FriCoordinateTopLevel.Coordinate.PointVec)
    (circleDenominators denominators flat :
      AspisV5FriCoordinateTopLevel.Coordinate.M31Vec)
    (output : AspisV5FriCoordinateTopLevel.Coordinate.Output)
    (hpoints : ReleasedPointListsEvidence layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points)
    (hcircle : AspisV5FriCoordinateDenominatorLoops.CirclePost circlePoints
      (circleDenominators, none))
    (hlines : AspisV5FriCoordinateDenominatorLoops.ThreeLineLayerPost
      circleDenominators line1Points line2Points line3Points
      (denominators, none))
    (hinverses : AspisV5FriCoordinateInverseLoops.BatchInverseEvidence
      denominators flat)
    (houtput : AspisV5FriCoordinateOutputLoops.AcceptedOutputEvidence
      layer0 line1 line2 line3 flat line3Points output) :
    ∀ ordinal, ordinal < line2.val.length →
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.later.val[1]!.val[ordinal]!.val[0]! =
        (2 * (ReleasedLine2Expected line2 ordinal).1.1)⁻¹ ∧
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.later.val[1]!.val[ordinal]!.val[1]! =
        (2 * (ReleasedLine2Expected line2 ordinal).1.2)⁻¹ ∧
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.later.val[1]!.val[ordinal]!.val[2]! =
        (2 * (2 * (ReleasedLine2Expected line2 ordinal).1.1 ^ 2 - 1))⁻¹ := by
  intro ordinal hord
  rcases hcircle with ⟨hcircleLength, _hcircleCanonical, _hzero,
    _hcircleValues⟩
  have hlineValues :=
    AspisV5FriCoordinateDenominatorLoops.threeLineLayerPost_exact_values
      circleDenominators denominators line1Points line2Points line3Points
      hlines
  rcases hlineValues with
    ⟨hdenominatorLength, _hprefix, _hline1Values, hline2Values,
      _hline3Values⟩
  rcases hinverses with ⟨_hflatLength, _hflatCanonical, hflatValues⟩
  rcases houtput with ⟨_hcircleOutput, later0, later1, later2,
    hlater, _hlater0, hlater1, _hlater2, _hfinal⟩
  have hpointBound : ordinal < line2Points.val.length := by
    simpa [hpoints.line2Length] using hord
  have hstart : circleDenominators.val.length +
      3 * line1Points.val.length =
      2 * layer0.val.length + 3 * line1.val.length := by
    rw [hcircleLength, hpoints.circleLength, hpoints.line1Length]
  have hslot0 : circleDenominators.val.length +
      3 * line1Points.val.length + 3 * ordinal < denominators.val.length := by
    omega
  have hslot1 : circleDenominators.val.length +
      3 * line1Points.val.length + 3 * ordinal + 1 <
        denominators.val.length := by omega
  have hslot2 : circleDenominators.val.length +
      3 * line1Points.val.length + 3 * ordinal + 2 <
        denominators.val.length := by omega
  have houtput0 : output.later.val[1]!.val[ordinal]!.val[0]! =
      flat.val[circleDenominators.val.length +
        3 * line1Points.val.length + 3 * ordinal]! := by
    rw [hlater]
    change later1.val[ordinal]!.val[0]! = _
    rw [hlater1,
      AspisV5FriCoordinateOutputLoops.tripleOutput_get_zero flat
        (2 * layer0.val.length + 3 * line1.val.length)
        line2.val.length ordinal hord, ← hstart]
  have houtput1 : output.later.val[1]!.val[ordinal]!.val[1]! =
      flat.val[circleDenominators.val.length +
        3 * line1Points.val.length + 3 * ordinal + 1]! := by
    rw [hlater]
    change later1.val[ordinal]!.val[1]! = _
    rw [hlater1,
      AspisV5FriCoordinateOutputLoops.tripleOutput_get_one flat
        (2 * layer0.val.length + 3 * line1.val.length)
        line2.val.length ordinal hord, ← hstart]
  have houtput2 : output.later.val[1]!.val[ordinal]!.val[2]! =
      flat.val[circleDenominators.val.length +
        3 * line1Points.val.length + 3 * ordinal + 2]! := by
    rw [hlater]
    change later1.val[ordinal]!.val[2]! = _
    rw [hlater1,
      AspisV5FriCoordinateOutputLoops.tripleOutput_get_two flat
        (2 * layer0.val.length + 3 * line1.val.length)
        line2.val.length ordinal hord, ← hstart]
  have hmeaning := hpoints.line2 ordinal hpointBound
  have hx : AspisV5FriCoordinateFieldSemantics.m31Value
      line2Points.val[ordinal]!.x =
        (ReleasedLine2Expected line2 ordinal).1.1 :=
    congrArg Prod.fst hmeaning.2
  have hy : AspisV5FriCoordinateFieldSemantics.m31Value
      line2Points.val[ordinal]!.y =
        (ReleasedLine2Expected line2 ordinal).1.2 :=
    congrArg Prod.snd hmeaning.2
  have hvalues := hline2Values ordinal hpointBound
  constructor
  · rw [houtput0, hflatValues _ hslot0, hvalues.1, hx]
  · constructor
    · rw [houtput1, hflatValues _ hslot1, hvalues.2.1, hy]
    · rw [houtput2, hflatValues _ hslot2, hvalues.2.2, hx]

/-- Exact released inverse coordinates for the third line layer. -/
theorem accepted_output_line3_exact
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points :
      AspisV5FriCoordinateTopLevel.Coordinate.PointVec)
    (circleDenominators denominators flat :
      AspisV5FriCoordinateTopLevel.Coordinate.M31Vec)
    (output : AspisV5FriCoordinateTopLevel.Coordinate.Output)
    (hpoints : ReleasedPointListsEvidence layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points)
    (hcircle : AspisV5FriCoordinateDenominatorLoops.CirclePost circlePoints
      (circleDenominators, none))
    (hlines : AspisV5FriCoordinateDenominatorLoops.ThreeLineLayerPost
      circleDenominators line1Points line2Points line3Points
      (denominators, none))
    (hinverses : AspisV5FriCoordinateInverseLoops.BatchInverseEvidence
      denominators flat)
    (houtput : AspisV5FriCoordinateOutputLoops.AcceptedOutputEvidence
      layer0 line1 line2 line3 flat line3Points output) :
    ∀ ordinal, ordinal < line3.val.length →
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.later.val[2]!.val[ordinal]!.val[0]! =
        (2 * (ReleasedLine3Expected line3 ordinal).1.1)⁻¹ ∧
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.later.val[2]!.val[ordinal]!.val[1]! =
        (2 * (ReleasedLine3Expected line3 ordinal).1.2)⁻¹ ∧
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.later.val[2]!.val[ordinal]!.val[2]! =
        (2 * (2 * (ReleasedLine3Expected line3 ordinal).1.1 ^ 2 - 1))⁻¹ := by
  intro ordinal hord
  rcases hcircle with ⟨hcircleLength, _hcircleCanonical, _hzero,
    _hcircleValues⟩
  have hlineValues :=
    AspisV5FriCoordinateDenominatorLoops.threeLineLayerPost_exact_values
      circleDenominators denominators line1Points line2Points line3Points
      hlines
  rcases hlineValues with
    ⟨hdenominatorLength, _hprefix, _hline1Values, _hline2Values,
      hline3Values⟩
  rcases hinverses with ⟨_hflatLength, _hflatCanonical, hflatValues⟩
  rcases houtput with ⟨_hcircleOutput, later0, later1, later2,
    hlater, _hlater0, _hlater1, hlater2, _hfinal⟩
  have hpointBound : ordinal < line3Points.val.length := by
    simpa [hpoints.line3Length] using hord
  have hstart : circleDenominators.val.length +
      3 * line1Points.val.length + 3 * line2Points.val.length =
      2 * layer0.val.length + 3 * line1.val.length +
        3 * line2.val.length := by
    rw [hcircleLength, hpoints.circleLength, hpoints.line1Length,
      hpoints.line2Length]
  have hslot0 : circleDenominators.val.length +
      3 * line1Points.val.length + 3 * line2Points.val.length +
        3 * ordinal < denominators.val.length := by omega
  have hslot1 : circleDenominators.val.length +
      3 * line1Points.val.length + 3 * line2Points.val.length +
        3 * ordinal + 1 < denominators.val.length := by omega
  have hslot2 : circleDenominators.val.length +
      3 * line1Points.val.length + 3 * line2Points.val.length +
        3 * ordinal + 2 < denominators.val.length := by omega
  have houtput0 : output.later.val[2]!.val[ordinal]!.val[0]! =
      flat.val[circleDenominators.val.length +
        3 * line1Points.val.length + 3 * line2Points.val.length +
          3 * ordinal]! := by
    rw [hlater]
    change later2.val[ordinal]!.val[0]! = _
    rw [hlater2,
      AspisV5FriCoordinateOutputLoops.tripleOutput_get_zero flat
        (2 * layer0.val.length + 3 * line1.val.length +
          3 * line2.val.length) line3.val.length ordinal hord, ← hstart]
  have houtput1 : output.later.val[2]!.val[ordinal]!.val[1]! =
      flat.val[circleDenominators.val.length +
        3 * line1Points.val.length + 3 * line2Points.val.length +
          3 * ordinal + 1]! := by
    rw [hlater]
    change later2.val[ordinal]!.val[1]! = _
    rw [hlater2,
      AspisV5FriCoordinateOutputLoops.tripleOutput_get_one flat
        (2 * layer0.val.length + 3 * line1.val.length +
          3 * line2.val.length) line3.val.length ordinal hord, ← hstart]
  have houtput2 : output.later.val[2]!.val[ordinal]!.val[2]! =
      flat.val[circleDenominators.val.length +
        3 * line1Points.val.length + 3 * line2Points.val.length +
          3 * ordinal + 2]! := by
    rw [hlater]
    change later2.val[ordinal]!.val[2]! = _
    rw [hlater2,
      AspisV5FriCoordinateOutputLoops.tripleOutput_get_two flat
        (2 * layer0.val.length + 3 * line1.val.length +
          3 * line2.val.length) line3.val.length ordinal hord, ← hstart]
  have hmeaning := hpoints.line3 ordinal hpointBound
  have hx : AspisV5FriCoordinateFieldSemantics.m31Value
      line3Points.val[ordinal]!.x =
        (ReleasedLine3Expected line3 ordinal).1.1 :=
    congrArg Prod.fst hmeaning.2
  have hy : AspisV5FriCoordinateFieldSemantics.m31Value
      line3Points.val[ordinal]!.y =
        (ReleasedLine3Expected line3 ordinal).1.2 :=
    congrArg Prod.snd hmeaning.2
  have hvalues := hline3Values ordinal hpointBound
  constructor
  · rw [houtput0, hflatValues _ hslot0, hvalues.1, hx]
  · constructor
    · rw [houtput1, hflatValues _ hslot1, hvalues.2.1, hy]
    · rw [houtput2, hflatValues _ hslot2, hvalues.2.2, hx]

/-- The twice-doubled x coordinate of a released third-line point is the
released final-domain x coordinate at the same parent index. -/
theorem releasedLine3Expected_finalX
    (indices : Slice Std.U32) (hindices : IndicesBelow indices 2048)
    (ordinal : Nat) (hordinal : ordinal < indices.val.length) :
    2 * (2 * (ReleasedLine3Expected indices ordinal).1.1 ^ 2 - 1) ^ 2 - 1 =
      AspisV5FriReleasedLineGeometry.storedLine11X
        (Fin.ofNat 2048 indices.val[ordinal]!.val) := by
  have hindex := hindices ordinal hordinal
  let parent : Fin 2048 := ⟨indices.val[ordinal]!.val, hindex⟩
  have hparent : Fin.ofNat 2048 indices.val[ordinal]!.val = parent :=
    finOfNat_eq_of_lt 2048 indices.val[ordinal]!.val hindex
  rw [hparent]
  unfold ReleasedLine3Expected releasedLine3Point
  rw [hparent]
  change
    AspisCircleTensorBinding.doubledFactor
        (AspisCircleTensorBinding.doubledFactor
          (AspisV5FriReleasedLineGeometry.storedLine13X
            (AspisV5ComponentCConcreteFoldLinearity.childIndex parent 0)) 1) 1 =
      AspisV5FriReleasedLineGeometry.storedLine11X parent
  rw [AspisV5FriReleasedLineGeometry.storedLine13_t2_slot0,
    AspisV5FriReleasedLineGeometry.storedLine12_t2]

/-- The final output vector contains the exact released final-domain point for
each accepted third-line query. -/
theorem accepted_output_final_x_exact
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points :
      AspisV5FriCoordinateTopLevel.Coordinate.PointVec)
    (flat : AspisV5FriCoordinateTopLevel.Coordinate.M31Vec)
    (output : AspisV5FriCoordinateTopLevel.Coordinate.Output)
    (hline3 : IndicesBelow line3 2048)
    (hpoints : ReleasedPointListsEvidence layer0 line1 line2 line3
      circlePoints line1Points line2Points line3Points)
    (houtput : AspisV5FriCoordinateOutputLoops.AcceptedOutputEvidence
      layer0 line1 line2 line3 flat line3Points output) :
    ∀ ordinal, ordinal < line3.val.length →
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.final_x.val[ordinal]! =
        AspisV5FriReleasedLineGeometry.storedLine11X
          (Fin.ofNat 2048 line3.val[ordinal]!.val) := by
  intro ordinal hord
  have hpointBound : ordinal < line3Points.val.length := by
    simpa [hpoints.line3Length] using hord
  rcases houtput with ⟨_hcircle, _later0, _later1, _later2,
    _hlater, _hlater0, _hlater1, _hlater2, hfinal⟩
  have hmeaning := hpoints.line3 ordinal hpointBound
  have hx : AspisV5FriCoordinateFieldSemantics.m31Value
      line3Points.val[ordinal]!.x =
        (ReleasedLine3Expected line3 ordinal).1.1 :=
    congrArg Prod.fst hmeaning.2
  rw [hfinal.2.2 ordinal hpointBound,
    AspisV5FriCoordinateOutputLoops.finalXFormula, hx,
    releasedLine3Expected_finalX line3 hline3 ordinal hord]

/-- The released circle point representation uses exactly the two evaluation
coordinates named by the mathematical V5 schedule. -/
theorem releasedCircleExpected_coordinates
    (indices : Slice Std.U32) (ordinal : Nat) :
    (ReleasedCircleExpected indices ordinal).1.1 =
        AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.circleX
          (Fin.ofNat 131072 indices.val[ordinal]!.val) ∧
    (ReleasedCircleExpected indices ordinal).1.2 =
        AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.circleY
          (Fin.ofNat 131072 indices.val[ordinal]!.val) := by
  constructor <;>
    simp only [ReleasedCircleExpected, releasedCirclePoint,
      AspisV5FriReleasedLineGeometry.releasedEvaluationPoints,
      AspisV5FriReleasedLineGeometry.releasedLinePoints,
      AspisCircleGroupOrder.X]

/-- The three denominators derived from a first-line source point are exactly
the three evaluation coordinates named by the mathematical V5 schedule. -/
theorem releasedLine1Expected_coordinates
    (indices : Slice Std.U32) (ordinal : Nat) :
    (ReleasedLine1Expected indices ordinal).1.1 =
        AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.line1
          (Fin.ofNat 32768 indices.val[ordinal]!.val) 0 ∧
    (ReleasedLine1Expected indices ordinal).1.2 =
        AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.line1
          (Fin.ofNat 32768 indices.val[ordinal]!.val) 1 ∧
    2 * (ReleasedLine1Expected indices ordinal).1.1 ^ 2 - 1 =
        AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.line1
          (Fin.ofNat 32768 indices.val[ordinal]!.val) 2 := by
  have hpoint : ReleasedLine1Expected indices ordinal =
      AspisV5FriReleasedLineGeometry.storedLine17Point
        (AspisV5ComponentCConcreteFoldLinearity.childIndex
          (Fin.ofNat 32768 indices.val[ordinal]!.val) 0) := rfl
  have hcoordinates :=
    AspisV5FriCoordinateMathematics.storedLine17_point_coordinates
      (Fin.ofNat 32768 indices.val[ordinal]!.val)
  constructor
  · rw [hpoint]
    exact hcoordinates.1
  · constructor
    · rw [hpoint]
      exact hcoordinates.2.1
    · rw [hpoint]
      exact hcoordinates.2.2

/-- Exact schedule coordinates for a second-line source point. -/
theorem releasedLine2Expected_coordinates
    (indices : Slice Std.U32) (ordinal : Nat) :
    (ReleasedLine2Expected indices ordinal).1.1 =
        AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.line2
          (Fin.ofNat 8192 indices.val[ordinal]!.val) 0 ∧
    (ReleasedLine2Expected indices ordinal).1.2 =
        AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.line2
          (Fin.ofNat 8192 indices.val[ordinal]!.val) 1 ∧
    2 * (ReleasedLine2Expected indices ordinal).1.1 ^ 2 - 1 =
        AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.line2
          (Fin.ofNat 8192 indices.val[ordinal]!.val) 2 := by
  have hpoint : ReleasedLine2Expected indices ordinal =
      AspisV5FriReleasedLineGeometry.storedLine15Point
        (AspisV5ComponentCConcreteFoldLinearity.childIndex
          (Fin.ofNat 8192 indices.val[ordinal]!.val) 0) := rfl
  have hcoordinates :=
    AspisV5FriCoordinateMathematics.storedLine15_point_coordinates
      (Fin.ofNat 8192 indices.val[ordinal]!.val)
  constructor
  · rw [hpoint]
    exact hcoordinates.1
  · constructor
    · rw [hpoint]
      exact hcoordinates.2.1
    · rw [hpoint]
      exact hcoordinates.2.2

/-- Exact schedule coordinates for a third-line source point. -/
theorem releasedLine3Expected_coordinates
    (indices : Slice Std.U32) (ordinal : Nat) :
    (ReleasedLine3Expected indices ordinal).1.1 =
        AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.line3
          (Fin.ofNat 2048 indices.val[ordinal]!.val) 0 ∧
    (ReleasedLine3Expected indices ordinal).1.2 =
        AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.line3
          (Fin.ofNat 2048 indices.val[ordinal]!.val) 1 ∧
    2 * (ReleasedLine3Expected indices ordinal).1.1 ^ 2 - 1 =
        AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.line3
          (Fin.ofNat 2048 indices.val[ordinal]!.val) 2 := by
  have hpoint : ReleasedLine3Expected indices ordinal =
      AspisV5FriReleasedLineGeometry.storedLine13Point
        (AspisV5ComponentCConcreteFoldLinearity.childIndex
          (Fin.ofNat 2048 indices.val[ordinal]!.val) 0) := rfl
  have hcoordinates :=
    AspisV5FriCoordinateMathematics.storedLine13_point_coordinates
      (Fin.ofNat 2048 indices.val[ordinal]!.val)
  constructor
  · rw [hpoint]
    exact hcoordinates.1
  · constructor
    · rw [hpoint]
      exact hcoordinates.2.1
    · rw [hpoint]
      exact hcoordinates.2.2

/-- Exact mathematical meaning of every coordinate returned by the translated
release adapter, at the source index occupying each output ordinal. -/
structure ReleasedCoordinateOutputEvidence
    (layer0 line1 line2 line3 : Slice Std.U32)
    (output : AspisV5FriCoordinateTopLevel.Coordinate.Output) : Prop where
  circleCanonical : ∀ ordinal, ordinal < layer0.val.length →
    AspisV5FriCoordinateFieldSemantics.canonicalM31
        output.circle.val[ordinal]!.val[0]! ∧
      AspisV5FriCoordinateFieldSemantics.canonicalM31
        output.circle.val[ordinal]!.val[1]!
  line1Canonical : ∀ ordinal, ordinal < line1.val.length →
    ∀ slot : Fin 3,
      AspisV5FriCoordinateFieldSemantics.canonicalM31
        output.later.val[0]!.val[ordinal]!.val[slot.val]!
  line2Canonical : ∀ ordinal, ordinal < line2.val.length →
    ∀ slot : Fin 3,
      AspisV5FriCoordinateFieldSemantics.canonicalM31
        output.later.val[1]!.val[ordinal]!.val[slot.val]!
  line3Canonical : ∀ ordinal, ordinal < line3.val.length →
    ∀ slot : Fin 3,
      AspisV5FriCoordinateFieldSemantics.canonicalM31
        output.later.val[2]!.val[ordinal]!.val[slot.val]!
  finalXCanonical : ∀ ordinal, ordinal < line3.val.length →
    AspisV5FriCoordinateFieldSemantics.canonicalM31
      output.final_x.val[ordinal]!
  circle : ∀ ordinal, ordinal < layer0.val.length →
    AspisV5FriCoordinateFieldSemantics.m31Value
        output.circle.val[ordinal]!.val[0]! =
      (2 * AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.circleX
        (Fin.ofNat 131072 layer0.val[ordinal]!.val))⁻¹ ∧
    AspisV5FriCoordinateFieldSemantics.m31Value
        output.circle.val[ordinal]!.val[1]! =
      (2 * AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.circleY
        (Fin.ofNat 131072 layer0.val[ordinal]!.val))⁻¹
  line1Values : ∀ ordinal, ordinal < line1.val.length →
    ∀ slot : Fin 3,
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.later.val[0]!.val[ordinal]!.val[slot.val]! =
        (2 * AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.line1
          (Fin.ofNat 32768 line1.val[ordinal]!.val) slot)⁻¹
  line2Values : ∀ ordinal, ordinal < line2.val.length →
    ∀ slot : Fin 3,
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.later.val[1]!.val[ordinal]!.val[slot.val]! =
        (2 * AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.line2
          (Fin.ofNat 8192 line2.val[ordinal]!.val) slot)⁻¹
  line3Values : ∀ ordinal, ordinal < line3.val.length →
    ∀ slot : Fin 3,
      AspisV5FriCoordinateFieldSemantics.m31Value
          output.later.val[2]!.val[ordinal]!.val[slot.val]! =
        (2 * AspisV5FriReleasedLineGeometry.releasedEvaluationPoints.line3
          (Fin.ofNat 2048 line3.val[ordinal]!.val) slot)⁻¹
  finalX : ∀ ordinal, ordinal < line3.val.length →
    AspisV5FriCoordinateFieldSemantics.m31Value
        output.final_x.val[ordinal]! =
      AspisV5FriReleasedLineGeometry.storedLine11X
        (Fin.ofNat 2048 line3.val[ordinal]!.val)

/-- End-to-end theorem for the translated release coordinate function.  If
the four source point helpers accept valid released index lists, the top-level
function succeeds and every returned coordinate has the exact value used by
the mathematical FRI schedule. -/
theorem extracted_released_coordinate_tables_exact
    (layer0 line1 line2 line3 : Slice Std.U32)
    (circlePoints line1Points line2Points line3Points :
      AspisV5FriCoordinateTopLevel.Coordinate.PointVec)
    (hlayer0 : IndicesBelow layer0 131072)
    (hline1 : IndicesBelow line1 32768)
    (hline2 : IndicesBelow line2 8192)
    (hline3 : IndicesBelow line3 2048)
    (hcircleCall :
      V5FriCoordinateAdapter.aspis_core.circle_fri.selected_circle_fiber_points_shared
          19#u32 layer0 = .ok (circlePoints, true))
    (hline1Call :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          layer0 (alloc.vec.Vec.deref circlePoints) line1 1#u8 =
        .ok (line1Points, true))
    (hline2Call :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          line1 (alloc.vec.Vec.deref line1Points) line2 2#u8 =
        .ok (line2Points, true))
    (hline3Call :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          line2 (alloc.vec.Vec.deref line2Points) line3 2#u8 =
        .ok (line3Points, true))
    (hcircleNonempty : 0 < layer0.val.length)
    (hcapacity : 2 * layer0.val.length +
        3 * (line1.val.length + line2.val.length + line3.val.length) ≤
          Std.Usize.max) :
    ∃ output,
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle
          19#u32 layer0 line1 line2 line3 = .ok (.Ok output) ∧
      ReleasedCoordinateOutputEvidence layer0 line1 line2 line3 output := by
  have hpoints := accepted_point_helpers_represent_released
    layer0 line1 line2 line3 circlePoints line1Points line2Points line3Points
    hlayer0 hline1 hline2 hline3 hcircleCall hline1Call hline2Call hline3Call
  rcases extracted_released_coordinate_path_exact
      layer0 line1 line2 line3 circlePoints line1Points line2Points line3Points
      hlayer0 hline1 hline2 hline3 hcircleCall hline1Call hline2Call
      hline3Call hcircleNonempty hcapacity with
    ⟨circleDenominators, denominators, flat, output, hrun, hcircle,
      hlines, hinverses, houtput⟩
  have hlineValues :=
    AspisV5FriCoordinateDenominatorLoops.threeLineLayerPost_exact_values
      circleDenominators denominators line1Points line2Points line3Points
      hlines
  have hcircleLength : circleDenominators.val.length ≤
      denominators.val.length := by
    rcases hlineValues with ⟨hlength, _⟩
    omega
  have hprefix := hlineValues.2.1
  have hcircleExact := accepted_output_circle_exact
    layer0 line1 line2 line3 circlePoints line1Points line2Points line3Points
    circleDenominators denominators flat output hpoints hcircle hinverses
    hcircleLength hprefix houtput
  have hline1Exact := accepted_output_line1_exact
    layer0 line1 line2 line3 circlePoints line1Points line2Points line3Points
    circleDenominators denominators flat output hpoints hcircle hlines
    hinverses houtput
  have hline2Exact := accepted_output_line2_exact
    layer0 line1 line2 line3 circlePoints line1Points line2Points line3Points
    circleDenominators denominators flat output hpoints hcircle hlines
    hinverses houtput
  have hline3Exact := accepted_output_line3_exact
    layer0 line1 line2 line3 circlePoints line1Points line2Points line3Points
    circleDenominators denominators flat output hpoints hcircle hlines
    hinverses houtput
  have hfinalExact := accepted_output_final_x_exact
    layer0 line1 line2 line3 circlePoints line1Points line2Points line3Points
    flat output hline3 hpoints houtput
  have hflatLength : flat.val.length =
      2 * layer0.val.length + 3 * line1.val.length +
        3 * line2.val.length + 3 * line3.val.length := by
    calc
      flat.val.length = denominators.val.length := hinverses.1
      _ = circleDenominators.val.length + 3 * line1Points.val.length +
          3 * line2Points.val.length + 3 * line3Points.val.length :=
        hlineValues.1
      _ = 2 * layer0.val.length + 3 * line1.val.length +
          3 * line2.val.length + 3 * line3.val.length := by
        rw [hcircle.1, hpoints.circleLength, hpoints.line1Length,
          hpoints.line2Length, hpoints.line3Length]
  have hflatCanonical := hinverses.2.1
  obtain ⟨later0, later1, later2, hlater, hlater0, hlater1, hlater2,
      hfinalPost⟩ := houtput.2
  have hlater0Out : output.later.val[0]! = later0 := by
    rw [hlater]
    rfl
  have hlater1Out : output.later.val[1]! = later1 := by
    rw [hlater]
    rfl
  have hlater2Out : output.later.val[2]! = later2 := by
    rw [hlater]
    rfl
  refine ⟨output, hrun, {
    circleCanonical := ?_
    line1Canonical := ?_
    line2Canonical := ?_
    line3Canonical := ?_
    finalXCanonical := ?_
    circle := ?_
    line1Values := ?_
    line2Values := ?_
    line3Values := ?_
    finalX := hfinalExact }⟩
  · intro ordinal hord
    constructor
    · rw [houtput.1,
        AspisV5FriCoordinateOutputLoops.pairOutput_get_zero flat 0
          layer0.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [houtput.1,
        AspisV5FriCoordinateOutputLoops.pairOutput_get_one flat 0
          layer0.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
  · intro ordinal hord slot
    rw [hlater0Out, hlater0]
    fin_cases slot
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_zero flat
        (2 * layer0.val.length) line1.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_one flat
        (2 * layer0.val.length) line1.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_two flat
        (2 * layer0.val.length) line1.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
  · intro ordinal hord slot
    rw [hlater1Out, hlater1]
    fin_cases slot
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_zero flat
        (2 * layer0.val.length + 3 * line1.val.length)
          line2.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_one flat
        (2 * layer0.val.length + 3 * line1.val.length)
          line2.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_two flat
        (2 * layer0.val.length + 3 * line1.val.length)
          line2.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
  · intro ordinal hord slot
    rw [hlater2Out, hlater2]
    fin_cases slot
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_zero flat
        (2 * layer0.val.length + 3 * line1.val.length +
          3 * line2.val.length) line3.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_one flat
        (2 * layer0.val.length + 3 * line1.val.length +
          3 * line2.val.length) line3.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
    · rw [AspisV5FriCoordinateOutputLoops.tripleOutput_get_two flat
        (2 * layer0.val.length + 3 * line1.val.length +
          3 * line2.val.length) line3.val.length ordinal hord]
      apply hflatCanonical
      rw [hflatLength]
      omega
  · intro ordinal hord
    apply hfinalPost.2.1 ordinal
    rw [hfinalPost.1, hpoints.line3Length]
    exact hord
  · intro ordinal hord
    have h := hcircleExact ordinal hord
    have hcoordinates := releasedCircleExpected_coordinates layer0 ordinal
    simpa only [hcoordinates.1, hcoordinates.2] using h
  · intro ordinal hord slot
    have h := hline1Exact ordinal hord
    have hcoordinates := releasedLine1Expected_coordinates line1 ordinal
    fin_cases slot
    · exact h.1.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.1))
    · exact h.2.1.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.2.1))
    · exact h.2.2.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.2.2))
  · intro ordinal hord slot
    have h := hline2Exact ordinal hord
    have hcoordinates := releasedLine2Expected_coordinates line2 ordinal
    fin_cases slot
    · exact h.1.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.1))
    · exact h.2.1.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.2.1))
    · exact h.2.2.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.2.2))
  · intro ordinal hord slot
    have h := hline3Exact ordinal hord
    have hcoordinates := releasedLine3Expected_coordinates line3 ordinal
    fin_cases slot
    · exact h.1.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.1))
    · exact h.2.1.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.2.1))
    · exact h.2.2.trans (congrArg Inv.inv (congrArg (2 * ·)
        hcoordinates.2.2))

/-- Every accepted result of the translated release coordinate function has
the exact released mathematical meaning.  Acceptance itself exposes the four
successful point-helper calls; determinism then identifies the independently
proved exact result with the result returned by this call. -/
theorem accepted_released_coordinate_tables_exact
    (layer0 line1 line2 line3 : Slice Std.U32)
    (output : AspisV5FriCoordinateTopLevel.Coordinate.Output)
    (hlayer0 : IndicesBelow layer0 131072)
    (hline1 : IndicesBelow line1 32768)
    (hline2 : IndicesBelow line2 8192)
    (hline3 : IndicesBelow line3 2048)
    (hcircleNonempty : 0 < layer0.val.length)
    (hcapacity : 2 * layer0.val.length +
        3 * (line1.val.length + line2.val.length + line3.val.length) ≤
          Std.Usize.max)
    (hrun :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle
          19#u32 layer0 line1 line2 line3 = .ok (.Ok output)) :
    ReleasedCoordinateOutputEvidence layer0 line1 line2 line3 output := by
  have hsource := hrun
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle
    at hsource
  norm_num [aspis_core.params.CIRCLE_LOG_ORDER,
    Std.lift, UScalar.lt_equiv, UScalar.size, U32.size, U32.numBits] at hsource
  generalize hcircleCall :
      V5FriCoordinateAdapter.aspis_core.circle_fri.selected_circle_fiber_points_shared
        19#u32 layer0 = circleResult at hsource
  cases circleResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hsource
  | div => simp [Bind.bind, Aeneas.Std.bind] at hsource
  | ok circlePair =>
    rcases circlePair with ⟨circlePoints, circleValid⟩
    simp only [bind_tc_ok] at hsource
    cases hcircleValid : circleValid with
    | false => simp [hcircleValid] at hsource
    | true =>
      simp only [hcircleValid, if_true] at hsource
      generalize hline1Call :
          V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
            layer0 (alloc.vec.Vec.deref circlePoints) line1 1#u8 =
              line1Result at hsource
      cases line1Result with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hsource
      | div => simp [Bind.bind, Aeneas.Std.bind] at hsource
      | ok line1Pair =>
        rcases line1Pair with ⟨line1Points, line1Valid⟩
        simp only [bind_tc_ok] at hsource
        cases hline1Valid : line1Valid with
        | false => simp [hline1Valid] at hsource
        | true =>
          simp only [hline1Valid, if_true] at hsource
          generalize hline2Call :
              V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
                line1 (alloc.vec.Vec.deref line1Points) line2 2#u8 =
                  line2Result at hsource
          cases line2Result with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hsource
          | div => simp [Bind.bind, Aeneas.Std.bind] at hsource
          | ok line2Pair =>
            rcases line2Pair with ⟨line2Points, line2Valid⟩
            simp only [bind_tc_ok] at hsource
            cases hline2Valid : line2Valid with
            | false => simp [hline2Valid] at hsource
            | true =>
              simp only [hline2Valid, if_true] at hsource
              generalize hline3Call :
                  V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
                    line2 (alloc.vec.Vec.deref line2Points) line3 2#u8 =
                      line3Result at hsource
              cases line3Result with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hsource
              | div => simp [Bind.bind, Aeneas.Std.bind] at hsource
              | ok line3Pair =>
                rcases line3Pair with ⟨line3Points, line3Valid⟩
                simp only [bind_tc_ok] at hsource
                cases hline3Valid : line3Valid with
                | false => simp [hline3Valid] at hsource
                | true =>
                  have hcircleCallExact :
                      V5FriCoordinateAdapter.aspis_core.circle_fri.selected_circle_fiber_points_shared
                          19#u32 layer0 = .ok (circlePoints, true) := by
                    simpa [hcircleValid] using hcircleCall
                  have hline1CallExact :
                      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
                          layer0 (alloc.vec.Vec.deref circlePoints) line1 1#u8 =
                        .ok (line1Points, true) := by
                    simpa [hline1Valid] using hline1Call
                  have hline2CallExact :
                      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
                          line1 (alloc.vec.Vec.deref line1Points) line2 2#u8 =
                        .ok (line2Points, true) := by
                    simpa [hline2Valid] using hline2Call
                  have hline3CallExact :
                      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
                          line2 (alloc.vec.Vec.deref line2Points) line3 2#u8 =
                        .ok (line3Points, true) := by
                    simpa [hline3Valid] using hline3Call
                  rcases extracted_released_coordinate_tables_exact
                      layer0 line1 line2 line3 circlePoints line1Points
                      line2Points line3Points hlayer0 hline1 hline2 hline3
                      hcircleCallExact hline1CallExact hline2CallExact
                      hline3CallExact hcircleNonempty hcapacity with
                    ⟨exactOutput, hexactRun, hexactMeaning⟩
                  have heq : exactOutput = output := by
                    rw [hexactRun] at hrun
                    exact core.result.Result.Ok.inj (Result.ok.inj hrun)
                  simpa [heq] using hexactMeaning
#print axioms sourceNatural_eq_reverseBits17
#print axioms selectedExpectedPoint_eq_released
#print axioms circle_parentTransform_eq_releasedLine1
#print axioms line1_parentTransform_eq_releasedLine2
#print axioms line2_parentTransform_eq_releasedLine3
#print axioms circle_parent_expected_compatible
#print axioms line1_parent_expected_compatible
#print axioms line2_parent_expected_compatible
#print axioms selected_points_represent_released
#print axioms accepted_point_helpers_represent_released
#print axioms releasedCircleExpected_nonzero
#print axioms releasedLine1Expected_nonzero
#print axioms releasedLine2Expected_nonzero
#print axioms releasedLine3Expected_nonzero
#print axioms extracted_released_coordinate_path_exact
#print axioms accepted_output_circle_exact
#print axioms accepted_output_line1_exact
#print axioms accepted_output_line2_exact
#print axioms accepted_output_line3_exact
#print axioms releasedLine3Expected_finalX
#print axioms accepted_output_final_x_exact
#print axioms releasedCircleExpected_coordinates
#print axioms releasedLine1Expected_coordinates
#print axioms releasedLine2Expected_coordinates
#print axioms releasedLine3Expected_coordinates
#print axioms extracted_released_coordinate_tables_exact
#print axioms accepted_released_coordinate_tables_exact

end AspisV5FriCoordinateReleasedPointConnection
