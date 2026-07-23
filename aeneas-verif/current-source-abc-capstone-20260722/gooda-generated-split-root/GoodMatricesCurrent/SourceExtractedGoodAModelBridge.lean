import GoodMatricesCurrent.SourceExtractedEvenKernel
import GoodMatricesCurrent.SourceExtractedShiftChain
import AspisFormal.V5ComponentADeployedTerminalApplicability

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier
open Matrix

namespace GoodMatricesCurrent.SourceExtractedGoodAModelBridge

open AspisCircleRectangularMasking
open AspisCircleTensorBinding
open AspisV5AtomicComponentACorrespondence
open AspisV5ComponentATerminalRankPredicate
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5GoodGateSparseShift

abbrev LocalM31 := aspis_verifier.aspis_core.field.M31
abbrev ExactM31 := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev LocalVector := Array LocalM31 48#usize
abbrev LocalKernel := Array LocalM31 37#usize
abbrev LocalChain := alloc.vec.Vec LocalVector

abbrev Base := AspisV5ComponentADeployedTerminalApplicability.Base
abbrev Tower := AspisV5ComponentADeployedTerminalApplicability.Tower
abbrev Source := AspisV5ComponentADeployedTerminalApplicability.Source

namespace EvenKernel

abbrev arrayToExact :=
  GoodMatricesCurrent.SourceExtractedEvenKernel.arrayToExact48
abbrev CanonicalLocalVector :=
  GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalVector
abbrev CanonicalLocalKernel :=
  GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalKernel
abbrev evenKernelOrdinary :=
  GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary

end EvenKernel

namespace FixedSupport

abbrev arrayToExact :=
  GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact
abbrev CanonicalLocalVector :=
  GoodMatricesCurrent.SourceExtractedFixedSupport.CanonicalLocalVector
abbrev FixedSupportInput :=
  GoodMatricesCurrent.SourceExtractedFixedSupport.FixedSupportInput

end FixedSupport

/-- The duplicated source-extraction views of a width-48 runtime array are
definitionally the same exact vector. -/
theorem fixedSupport_arrayToExact_eq_evenKernel (values : LocalVector) :
    FixedSupport.arrayToExact values = EvenKernel.arrayToExact values := by
  rfl

/-- The duplicated source-extraction canonicality predicates agree. -/
theorem fixedSupport_canonical_iff_evenKernel (values : LocalVector) :
    FixedSupport.CanonicalLocalVector values ↔
      EvenKernel.CanonicalLocalVector values := by
  rfl

/-- The extracted even-kernel ordinary vector has degree support below 37.
This is independent of the remaining runtime-to-query-kernel seam. -/
theorem evenKernelOrdinary_supportedBelow (kernel : LocalKernel) :
    SupportedBelow 37 (EvenKernel.evenKernelOrdinary kernel) := by
  intro degree habove
  simp [EvenKernel.evenKernelOrdinary,
    GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary,
    habove]

/-- Exact semantics of all twelve runtime vectors returned by the generated
GoodA shifted-direction constructor. -/
def ExactShiftedDirections (kernel : LocalKernel)
    (directions : LocalChain) : Prop :=
  directions.val.length = 12 ∧
  ∀ shift : Fin 12,
    ∃ vector : LocalVector,
      directions.val[shift.val]? = some vector ∧
      FixedSupport.CanonicalLocalVector vector ∧
      FixedSupport.arrayToExact vector =
        convert
          (ordinaryShiftIter shift.val
            (EvenKernel.evenKernelOrdinary kernel))

/-- The actual generated wrapper returns twelve canonical vectors.  Runtime
entry `shift` is exactly the maintained ordinary-to-natural conversion of the
even kernel multiplied by `X^shift`; no unselected entry is hidden behind a
list-level abstraction. -/
theorem good_shifted_directions_exact_spec (kernel : LocalKernel)
    (hkernel : EvenKernel.CanonicalLocalKernel kernel) :
    ∃ directions : LocalChain,
      v5_cu_probe.good_gate_probe.good_shifted_directions kernel =
          .ok directions ∧
      ExactShiftedDirections kernel directions := by
  letI : NeZero (2 : ExactM31) := ⟨by decide⟩
  obtain ⟨base, hbaseCall, hbaseCanonical, hbaseExact⟩ :=
    GoodMatricesCurrent.SourceExtractedEvenKernel.even_kernel_to_natural_exact_spec
      kernel hkernel
  have hbaseCanonicalFixed :
      FixedSupport.CanonicalLocalVector base := by
    exact hbaseCanonical
  have hbaseExactFixed :
      FixedSupport.arrayToExact base =
        convert (EvenKernel.evenKernelOrdinary kernel) := by
    exact hbaseExact
  have hbaseShape : FixedSupport.FixedSupportInput base 0 := by
    refine ⟨hbaseCanonicalFixed, by omega, ?_⟩
    intro coordinate houtside
    calc
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact base
          coordinate =
          convert (EvenKernel.evenKernelOrdinary kernel) coordinate :=
        congrFun hbaseExactFixed coordinate
      _ = 0 :=
        GoodMatricesCurrent.SourceExtractedEvenKernel.convert_evenKernelOrdinary_fixed_support
          kernel coordinate (by simpa using houtside)
  obtain ⟨directions, hloop, hentries⟩ :=
    GoodMatricesCurrent.SourceExtractedShiftChain.shifted_directions_loop_exact_spec
      base hbaseShape
  let empty : LocalChain :=
    alloc.vec.Vec.with_capacity LocalVector
      v5_cu_probe.good_gate_probe.GOOD_A_SIZE
  have hemptyBound : empty.val.length < Std.Usize.max := by
    unfold empty alloc.vec.Vec.with_capacity alloc.vec.Vec.new
    rcases System.Platform.numBits_eq with hplatform | hplatform <;>
      norm_num [Std.Usize.max, Std.Usize.numBits, hplatform]
  obtain ⟨initial, hpush, hinitialValue⟩ :=
    WP.spec_imp_exists (alloc.vec.Vec.push_spec empty base hemptyBound)
  have hinitial :
      initial =
        GoodMatricesCurrent.SourceExtractedShiftChain.singletonChain base := by
    apply Subtype.ext
    simpa [GoodMatricesCurrent.SourceExtractedShiftChain.singletonChain,
      empty, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] using hinitialValue
  subst initial
  have hcall :
      v5_cu_probe.good_gate_probe.good_shifted_directions kernel =
        .ok directions := by
    unfold v5_cu_probe.good_gate_probe.good_shifted_directions
    rw [hbaseCall]
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let shifted_directions1 ← alloc.vec.Vec.push empty base
      v5_cu_probe.good_gate_probe.good_shifted_directions_loop
        shifted_directions1 base 1#usize) = _
    rw [hpush]
    simp only [Aeneas.Std.bind_tc_ok]
    exact hloop
  refine ⟨directions, hcall, hentries.1, ?_⟩
  intro shift
  obtain ⟨vector, hlookup, hcanonical, hexact⟩ :=
    hentries.2 shift.val shift.isLt
  refine ⟨vector, hlookup, hcanonical, ?_⟩
  calc
    FixedSupport.arrayToExact vector =
        sparseShiftIter shift.val (FixedSupport.arrayToExact base) := hexact
    _ = sparseShiftIter shift.val
          (convert (EvenKernel.evenKernelOrdinary kernel)) := by
      rw [hbaseExactFixed]
    _ = convert
          (ordinaryShiftIter shift.val
            (EvenKernel.evenKernelOrdinary kernel)) :=
      goodA_complete_shift_chain (EvenKernel.evenKernelOrdinary kernel)
        (evenKernelOrdinary_supportedBelow kernel) shift.val (by omega)

/-- Index of a natural coordinate in the first maintained GoodA block. -/
def firstBlockIndex (index : Fin 48) : Fin originalWidth :=
  ⟨index.val, by
    have h := index.isLt
    norm_num [originalWidth] at h ⊢
    omega⟩

/-- An ordinary width-48 vector placed in the first maintained GoodA block. -/
def xBlockOrdinary (ordinary : Fin 48 → Base) : Source :=
  ordinaryOfBlocks ordinary 0

/-- Index of a natural coordinate in the second maintained GoodA block. -/
def secondBlockIndex (index : Fin 48) : Fin originalWidth :=
  ⟨48 + index.val, by
    have h := index.isLt
    norm_num [originalWidth] at h ⊢
    omega⟩

/-- An ordinary width-48 vector placed in the second maintained GoodA block. -/
def yBlockOrdinary (ordinary : Fin 48 → Base) : Source :=
  ordinaryOfBlocks 0 ordinary

/-- The first block of the maintained deployed conversion is the exact
width-48 ordinary-to-natural map used by the generated constructor. -/
theorem deployedAConversion_xBlock (ordinary : Fin 48 → Base)
    (natural : Fin 48) :
    deployedAConversion (liftBaseCoins (xBlockOrdinary ordinary))
        (firstBlockIndex natural) =
      algebraMap Base Tower
        ((monomialToNatural Base 48).mulVec ordinary natural) := by
  rw [deployedAConversion, Matrix.mulVecLin_apply]
  unfold Matrix.mulVec dotProduct
  change (∑ j : Fin (48 + 48),
      deployedAConversionMatrix (firstBlockIndex natural) j *
        algebraMap Base Tower (xBlockOrdinary ordinary j)) = _
  rw [Fin.sum_univ_add]
  have hsecond :
      (∑ j : Fin 48,
        deployedAConversionMatrix (firstBlockIndex natural)
            (Fin.natAdd 48 j) *
          algebraMap Base Tower
            (xBlockOrdinary ordinary (Fin.natAdd 48 j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [show deployedAConversionMatrix (firstBlockIndex natural)
        (Fin.natAdd 48 j) = 0 by
      unfold deployedAConversionMatrix
      rw [if_neg]
      simp [firstBlockIndex, AspisCircleRectangularMasking.originalHalf]]
    simp
  rw [hsecond, add_zero]
  simp only [deployedAConversionMatrix, firstBlockIndex, withinBlock,
    xBlockOrdinary, ordinaryOfBlocks,
    AspisCircleRectangularMasking.originalHalf, Fin.val_castAdd,
    Fin.is_lt, ↓reduceIte]
  simp_rw [← map_mul]
  rw [map_sum]
  rfl

/-- The second block of the maintained deployed conversion is the same exact
width-48 ordinary-to-natural map. -/
theorem deployedAConversion_yBlock (ordinary : Fin 48 → Base)
    (natural : Fin 48) :
    deployedAConversion (liftBaseCoins (yBlockOrdinary ordinary))
        (secondBlockIndex natural) =
      algebraMap Base Tower
        ((monomialToNatural Base 48).mulVec ordinary natural) := by
  rw [deployedAConversion, Matrix.mulVecLin_apply]
  unfold Matrix.mulVec dotProduct
  change (∑ j : Fin (48 + 48),
      deployedAConversionMatrix (secondBlockIndex natural) j *
        algebraMap Base Tower (yBlockOrdinary ordinary j)) = _
  rw [Fin.sum_univ_add]
  have hfirst :
      (∑ j : Fin 48,
        deployedAConversionMatrix (secondBlockIndex natural)
            (Fin.castAdd 48 j) *
          algebraMap Base Tower
            (yBlockOrdinary ordinary (Fin.castAdd 48 j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [show deployedAConversionMatrix (secondBlockIndex natural)
        (Fin.castAdd 48 j) = 0 by
      unfold deployedAConversionMatrix
      rw [if_neg]
      simp [secondBlockIndex,
        AspisCircleRectangularMasking.originalHalf]]
    simp
  rw [hfirst, zero_add]
  have houtput : withinBlock (secondBlockIndex natural) = natural := by
    unfold withinBlock
    rw [dif_neg]
    · apply Fin.ext
      simp [secondBlockIndex,
        AspisCircleRectangularMasking.originalHalf]
    · simp [secondBlockIndex,
        AspisCircleRectangularMasking.originalHalf]
  have hord : ∀ j : Fin 48,
      withinBlock (Fin.natAdd 48 j) = j := by
    intro j
    unfold withinBlock
    rw [dif_neg]
    · apply Fin.ext
      simp [AspisCircleRectangularMasking.originalHalf]
    · simp [AspisCircleRectangularMasking.originalHalf]
  have hmatrix : ∀ j : Fin 48,
      deployedAConversionMatrix (secondBlockIndex natural)
          (Fin.natAdd 48 j) =
        algebraMap Base Tower ((monomialToNatural Base 48) natural j) := by
    intro j
    unfold deployedAConversionMatrix
    rw [if_pos]
    · rw [houtput, hord]
      rfl
    · simp [secondBlockIndex,
        AspisCircleRectangularMasking.originalHalf]
  have hinput : ∀ j : Fin 48,
      yBlockOrdinary ordinary (Fin.natAdd 48 j) = ordinary j := by
    intro j
    simp [yBlockOrdinary, ordinaryOfBlocks,
      AspisCircleRectangularMasking.originalHalf]
  simp_rw [hmatrix, hinput]
  simp_rw [← map_mul]
  rw [map_sum]

/-- This proposition names the one deliberately unproved executable/model
edge: which maintained ordinary vector the runtime kernel array encodes. -/
def RuntimeKernelMatchesOrdinary (kernel : LocalKernel)
    (ordinary : Fin 48 → Base) : Prop :=
  EvenKernel.evenKernelOrdinary kernel = ordinary

/-- One runtime direction, identified both exactly and as the image of either
block of the maintained deployed GoodA conversion. -/
def ExactDeployedShiftEntry (ordinary : Fin 48 → Base)
    (shift : Fin 12) (vector : LocalVector) : Prop :=
  FixedSupport.CanonicalLocalVector vector ∧
  FixedSupport.arrayToExact vector =
    convert (ordinaryShiftIter shift.val ordinary) ∧
  ∀ natural : Fin 48,
    deployedAConversion
        (liftBaseCoins
          (xBlockOrdinary (ordinaryShiftIter shift.val ordinary)))
        (firstBlockIndex natural) =
        algebraMap Base Tower (FixedSupport.arrayToExact vector natural) ∧
    deployedAConversion
        (liftBaseCoins
          (yBlockOrdinary (ordinaryShiftIter shift.val ordinary)))
        (secondBlockIndex natural) =
      algebraMap Base Tower (FixedSupport.arrayToExact vector natural)

/-- All twelve entries returned by the generated constructor, stated directly
in the maintained `deployedAConversion` image. -/
def ExactDeployedDirections (ordinary : Fin 48 → Base)
    (directions : LocalChain) : Prop :=
  directions.val.length = 12 ∧
  ∀ shift : Fin 12,
    ∃ vector : LocalVector,
      directions.val[shift.val]? = some vector ∧
      ExactDeployedShiftEntry ordinary shift vector

/-- Full generated-to-maintained bridge for the GoodA conversion chain.  The
runtime/model kernel equality is explicit; conditioned on it, each of the
twelve actual runtime array entries is exactly the corresponding image of
both diagonal blocks of `deployedAConversion`. -/
theorem good_shifted_directions_deployedAConversion_spec
    (kernel : LocalKernel) (ordinary : Fin 48 → Base)
    (hkernel : EvenKernel.CanonicalLocalKernel kernel)
    (hkernelModel : RuntimeKernelMatchesOrdinary kernel ordinary) :
    ∃ directions : LocalChain,
      v5_cu_probe.good_gate_probe.good_shifted_directions kernel =
          .ok directions ∧
      ExactDeployedDirections ordinary directions := by
  obtain ⟨directions, hcall, hlength, hentries⟩ :=
    good_shifted_directions_exact_spec kernel hkernel
  refine ⟨directions, hcall, hlength, ?_⟩
  intro shift
  obtain ⟨vector, hlookup, hcanonical, hexact⟩ := hentries shift
  have hexactModel :
      FixedSupport.arrayToExact vector =
        convert (ordinaryShiftIter shift.val ordinary) := by
    rw [← hkernelModel]
    exact hexact
  refine ⟨vector, hlookup, hcanonical, hexactModel, ?_⟩
  intro natural
  constructor
  · calc
      deployedAConversion
          (liftBaseCoins
            (xBlockOrdinary (ordinaryShiftIter shift.val ordinary)))
          (firstBlockIndex natural) =
          algebraMap Base Tower
            ((monomialToNatural Base 48).mulVec
              (ordinaryShiftIter shift.val ordinary) natural) :=
        deployedAConversion_xBlock
          (ordinaryShiftIter shift.val ordinary) natural
      _ = algebraMap Base Tower
          (FixedSupport.arrayToExact vector natural) := by
        simpa [convert] using
          congrArg (algebraMap Base Tower)
            (congrFun hexactModel natural).symm
  · calc
      deployedAConversion
          (liftBaseCoins
            (yBlockOrdinary (ordinaryShiftIter shift.val ordinary)))
          (secondBlockIndex natural) =
          algebraMap Base Tower
            ((monomialToNatural Base 48).mulVec
              (ordinaryShiftIter shift.val ordinary) natural) :=
        deployedAConversion_yBlock
          (ordinaryShiftIter shift.val ordinary) natural
      _ = algebraMap Base Tower
          (FixedSupport.arrayToExact vector natural) := by
        simpa [convert] using
          congrArg (algebraMap Base Tower)
            (congrFun hexactModel natural).symm

#print axioms fixedSupport_arrayToExact_eq_evenKernel
#print axioms fixedSupport_canonical_iff_evenKernel
#print axioms evenKernelOrdinary_supportedBelow
#print axioms good_shifted_directions_exact_spec
#print axioms deployedAConversion_xBlock
#print axioms deployedAConversion_yBlock
#print axioms good_shifted_directions_deployedAConversion_spec

end GoodMatricesCurrent.SourceExtractedGoodAModelBridge
