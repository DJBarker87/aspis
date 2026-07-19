import AspisFormal.V5FreezeAScheduleAvailability

/-!
# Component-A public terminal-rank predicate

This file closes the *definition-to-mathematics* part of the Component-A
terminal applicability gate without claiming an executable correspondence.
The reference predicate uses the *actual base-field source*: the 96 coins are
in `DeployedField` (M31), the coefficient-sum and q18 kernel equations are over
that field, and the three terminal values are in the supplied tower `L`.  The
fixed `L`-linear terminal model is evaluated only after coefficientwise
`algebraMap` lifting.  Acceptance therefore implies the scalar-extended
condition consumed by `V5ComponentARankCompletion`, but not conversely.

It is intentionally not replaced by the sufficient three-by-three determinant
test from that file: no equivalence between that smaller test and the exact
kernel restriction has been proved.  The predicate below is a function only of
the public q18 schedule and public transcript point, through fixed public
weight and terminal-triple models.  A witness is not an argument.

The all-zero counterexample is retained.  If the terminal model at the zero
transcript point is the actual Boolean triple selecting rows `0`, `1`, and
`12`, then every encoder supported in rows `896..991` is rejected.  Equality
between a Rust-derived q18/point/terminal triple and these Lean objects remains
an explicit Rust-to-Lean interface; SHA/RO reachability is likewise not proved
or assumed in the kernel.

The final section gives one concrete accepted base-field *mathematical model*
using the same coordinate-probe idea as the existing `probeTriple`.  It proves
the exact predicate is nonempty, but is explicitly not the deployed
multilinear terminal model and does not discharge executable applicability.
-/

namespace AspisV5ComponentATerminalRankPredicate

open AspisCircleDiscreteAvailability
open AspisCircleRectangularMasking
open AspisV5AtomicComponentACorrespondence
open AspisV5ComponentARankCompletion
open AspisV5FreezeAScheduleAvailability

/-! ## Public schedule data and fixed public models -/

/-- The ten public Fiat--Shamir coordinates used by the deployed relation
claims. -/
abbrev TranscriptPoint (L : Type*) := Fin 10 → L

/-- The data on which Component A's terminal applicability decision is allowed
to depend.  Deployment intends both fields to be publicly transcript-derived.
This record alone does not prove that derivation or its witness-independence;
those remain explicit transcript/Rust interfaces below. -/
structure PublicTerminalSchedule (L : Type*) where
  q18 : Fin queryCount → Fin fibreCount
  point : TranscriptPoint L

/-- A fixed public model of the aligned row-896 weights as a function of the
public q18 schedule.  Identifying this model with Rust remains a separate
correspondence premise. -/
abbrev PublicWeightModel :=
  (Fin queryCount → Fin fibreCount) → FibreIndex → DeployedField

/-- A fixed public model of the three terminal covectors derived from a public
ten-round point.  In deployment this is intended to be MLE evaluation at
`z`, `successor(z)`, and `xor12(z)` after the fixed Component-A encoder.
The exact Rust/encoder/layout equality is not asserted by this type. -/
abbrev PublicTerminalModel (L : Type*) [CommRing L] :=
  TranscriptPoint L → (Fin originalWidth → L) →ₗ[L] (Fin 3 → L)

/-! ## The exact reference predicate -/

/-- Coefficientwise inclusion of the actual M31 coin vector into the terminal
tower.  This is the only way the exact predicate feeds coins to the supplied
`L`-linear terminal model. -/
def liftBaseCoins
    {L : Type*} [CommRing L] [Algebra DeployedField L]
    (c : Fin originalWidth → DeployedField) : Fin originalWidth → L :=
  fun i => algebraMap DeployedField L (c i)

/-- Lifting base coins back into the base field is pointwise the identity.  The
proof uses uniqueness of ring homomorphisms out of `ZMod P`, so it does not
depend on which definitionally equal self-algebra instance was selected. -/
@[simp] theorem liftBaseCoins_self
    (c : Fin originalWidth → DeployedField) :
    liftBaseCoins (L := DeployedField) c = c := by
  have halgebra : algebraMap DeployedField DeployedField =
      RingHom.id DeployedField := Subsingleton.elim _ _
  funext i
  change algebraMap DeployedField DeployedField (c i) = c i
  rw [halgebra]
  rfl

/-- **Exact public terminal-rank predicate.**  This is the required
surjectivity of the deployed terminal triple restricted simultaneously to the
actual M31 atomic coefficient-sum hyperplane and the actual M31 q18
circle-evaluation kernel.  The target remains the three-coordinate tower view.
It is the reference definition, not a scalar-extension converse, generic-point
approximation, finite KAT, or sufficient minor test. -/
def ExactTerminalRankPredicate
    {L : Type*} [CommRing L] [Algebra DeployedField L]
    (weightModel : PublicWeightModel)
    (terminalModel : PublicTerminalModel L)
    (schedule : PublicTerminalSchedule L) : Prop :=
  ∀ t : Fin 3 → L, ∃ c : Fin originalWidth → DeployedField,
    (∑ i, c i) = 0 ∧
      (deployedFibreRectangularEval schedule.q18
        (weightModel schedule.q18)).mulVec c = 0 ∧
      terminalModel schedule.point (liftBaseCoins c) = t

/-- Unfolding gives the exact base-source coverage statement. -/
theorem exactTerminalRankPredicate_iff
    {L : Type*} [CommRing L] [Algebra DeployedField L]
    (weightModel : PublicWeightModel)
    (terminalModel : PublicTerminalModel L)
    (schedule : PublicTerminalSchedule L) :
    ExactTerminalRankPredicate weightModel terminalModel schedule ↔
      ∀ t : Fin 3 → L, ∃ c : Fin originalWidth → DeployedField,
        (∑ i, c i) = 0 ∧
          (deployedFibreRectangularEval schedule.q18
            (weightModel schedule.q18)).mulVec c = 0 ∧
          terminalModel schedule.point (liftBaseCoins c) = t :=
  Iff.rfl

/-- **Base-source acceptance implies the existing scalar-extended terminal
coverage premise.**  A base witness is lifted coefficientwise; its sum and q18
kernel equations transport through `algebraMap`.  The converse is deliberately
not claimed. -/
theorem accepted_implies_terminal_coverage
    {L : Type*} [CommRing L] [Algebra DeployedField L]
    (weightModel : PublicWeightModel)
    (terminalModel : PublicTerminalModel L)
    (schedule : PublicTerminalSchedule L)
    (haccepted : ExactTerminalRankPredicate weightModel terminalModel schedule) :
    EqTerminalTripleCoversDeployedKernel schedule.q18
      (weightModel schedule.q18) (terminalModel schedule.point) :=
by
  intro t
  obtain ⟨c, hsum, hquery, hterminal⟩ := haccepted t
  refine ⟨liftBaseCoins c, ?_, ?_, hterminal⟩
  · have hmap : (∑ i, liftBaseCoins (L := L) c i) =
        algebraMap DeployedField L (∑ i, c i) :=
      (map_sum (algebraMap DeployedField L) c Finset.univ).symm
    rw [hmap, hsum, map_zero]
  · funext row
    have hmap := RingHom.map_mulVec (algebraMap DeployedField L)
      (deployedFibreRectangularEval schedule.q18 (weightModel schedule.q18)) c row
    rw [hquery] at hmap
    simp only [Pi.zero_apply, map_zero] at hmap
    exact hmap.symm

/-- The decision is extensional in exactly the supplied schedule record.  This
is the kernel-level "no witness argument" fact, not a proof that runtime
transcript derivation is witness-independent. -/
theorem exactTerminalRankPredicate_public_ext
    {L : Type*} [CommRing L] [Algebra DeployedField L]
    (weightModel : PublicWeightModel)
    (terminalModel : PublicTerminalModel L)
    {left right : PublicTerminalSchedule L} (hpublic : left = right) :
    ExactTerminalRankPredicate weightModel terminalModel left ↔
      ExactTerminalRankPredicate weightModel terminalModel right := by
  subst right
  exact Iff.rfl

/-! ## Explicit executable-correspondence interfaces -/

/-- Exact equality of runtime-derived public schedule data with the Lean
schedule.  This is a Rust-to-Lean premise, not a theorem about SHA or the Rust
implementation. -/
def RuntimePublicScheduleCorrespondence
    {L : Type*}
    (runtimeQ18 : Fin queryCount → Fin fibreCount)
    (runtimePoint : TranscriptPoint L)
    (schedule : PublicTerminalSchedule L) : Prop :=
  runtimeQ18 = schedule.q18 ∧ runtimePoint = schedule.point

/-- Exact equality of the runtime aligned row weights with the fixed public
weight model at the runtime q18 schedule. -/
def RuntimeWeightCorrespondence
    (runtimeWeight : FibreIndex → DeployedField)
    (weightModel : PublicWeightModel)
    (runtimeQ18 : Fin queryCount → Fin fibreCount) : Prop :=
  runtimeWeight = weightModel runtimeQ18

/-- Exact equality of the runtime terminal covectors with the fixed public
terminal model at the transcript point.  PCS/Merkle binding, SHA/RO, entropy,
and any Fiat--Shamir compiler theorem remain separate computational
assumptions and are not encoded here. -/
def RuntimeTerminalTripleCorrespondence
    {L : Type*} [CommRing L] [Algebra DeployedField L]
    (runtimeTriple :
      (Fin originalWidth → DeployedField) →ₗ[DeployedField] (Fin 3 → L))
    (terminalModel : PublicTerminalModel L)
    (point : TranscriptPoint L) : Prop :=
  ∀ c, runtimeTriple c = terminalModel point (liftBaseCoins c)

/-! ## The retained all-zero regression tooth -/

/-- The all-zero ten-round point. -/
def allZeroPoint (L : Type*) [Zero L] : TranscriptPoint L :=
  fun _ => 0

/-- A public schedule at the all-zero point, with arbitrary public q18 fibres.
The existing counterexample is independent of q18. -/
def allZeroSchedule
    {L : Type*} [Zero L]
    (q18 : Fin queryCount → Fin fibreCount) : PublicTerminalSchedule L where
  q18 := q18
  point := allZeroPoint L

/-- **All-zero is rejected.**  The only equality premise identifies the fixed
public terminal model at zero with the already-kernel-checked deployed Boolean
triple on the supplied encoder.  Under the exact reserve-support property, the
predicate is false for every q18 schedule and every aligned weight model. -/
theorem allZero_exactTerminalRankPredicate_rejected
    {L : Type*} [Field L] [Algebra DeployedField L]
    (weightModel : PublicWeightModel)
    (terminalModel : PublicTerminalModel L)
    (q18 : Fin queryCount → Fin fibreCount)
    (encode : (Fin originalWidth → L) →ₗ[L]
      (Fin AspisCircleTensorBinding.traceRows → L))
    (hreserve : EncoderOutputsAlignedReserve encode)
    (hzero : terminalModel (allZeroPoint L) = inducedDegenerateEqTriple encode) :
    ¬ ExactTerminalRankPredicate weightModel terminalModel (allZeroSchedule q18) := by
  intro haccepted
  have hcoverage := accepted_implies_terminal_coverage weightModel terminalModel
    (allZeroSchedule q18) haccepted
  change EqTerminalTripleCoversDeployedKernel q18 (weightModel q18)
    (terminalModel (allZeroPoint L)) at hcoverage
  rw [hzero] at hcoverage
  exact (degenerate_eq_side_does_not_cover q18 (weightModel q18) encode hreserve)
    hcoverage

/-- The prior concrete-layout counterexample remains directly available: any
linear coefficient conversion followed by the aligned interleaved placement
fails exact terminal coverage at the all-zero point. -/
theorem allZero_reserved_conversion_counterexample_retained
    {L : Type*} [Field L] [Algebra DeployedField L]
    (q18 : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField)
    (conversion : (Fin originalWidth → L) →ₗ[L] (Fin originalWidth → L)) :
    ¬ EqTerminalTripleCoversDeployedKernel q18 weight
      (inducedDegenerateEqTriple ((alignedReserveEmbed L).comp conversion)) :=
  degenerate_eq_side_counterexample_for_any_reserved_conversion
    q18 weight conversion

/-! ## Mathematical non-vacuity, not deployment correspondence -/

/-- Unit aligned weights, fixed as a public function of q18. -/
def unitWeightModel : PublicWeightModel :=
  fun _ _ => 1

/-- Base-field coordinate probes at pure-x columns 37, 38, and 39. -/
def baseProbeTriple :
    (Fin originalWidth → DeployedField) →ₗ[DeployedField]
      (Fin 3 → DeployedField) :=
  LinearMap.pi fun p => LinearMap.proj (probeIndex p)

/-- The base-field probes packaged as a fixed public terminal model.  This
model deliberately ignores its point and is not the deployed MLE model. -/
def baseProbeTerminalModel : PublicTerminalModel DeployedField :=
  fun _ => baseProbeTriple

/-- Concrete base-field public data for the model non-vacuity witness. -/
def baseProbePublicSchedule : PublicTerminalSchedule DeployedField where
  q18 := sampleQueries
  point := allZeroPoint DeployedField

/-- The concrete q18 schedule in the non-vacuity witness is without
replacement. -/
theorem baseProbePublicSchedule_q18_injective :
    Function.Injective baseProbePublicSchedule.q18 :=
  sampleQueries_injective

/-- A base probe-matrix entry is the corresponding concrete kernel-shift
coefficient. -/
theorem baseProbe_tripleMatrix_apply (p i : Fin 3) :
    tripleMatrix (L := DeployedField) sampleQueries baseProbeTriple p i =
      (kernelShift sampleQueries ((i : ℕ) + 1)).coeff (37 + (p : ℕ)) := by
  show baseProbeTriple (kernelTripleVecL sampleQueries i) p = _
  simp only [baseProbeTriple, LinearMap.pi_apply, LinearMap.proj_apply]
  have hlt : ((probeIndex p : Fin originalWidth) : ℕ) < originalHalf := by
    have hp := p.isLt
    simp only [probeIndex, originalHalf]
    omega
  simp only [kernelTripleVecL, kernelTripleVec, xBlockEmbed, hlt, if_pos,
    Algebra.algebraMap_self_apply]
  rfl

/-- The base probe matrix has a unit diagonal. -/
theorem baseProbe_tripleMatrix_diag (p : Fin 3) :
    tripleMatrix (L := DeployedField) sampleQueries baseProbeTriple p p = 1 := by
  have harith : 37 + (p : ℕ) = 36 + ((p : ℕ) + 1) := by omega
  rw [baseProbe_tripleMatrix_apply, harith,
    kernelShift_coeff_top sampleQueries (by omega)]

/-- Entries below the base probe diagonal vanish. -/
theorem baseProbe_tripleMatrix_lower (p i : Fin 3)
    (h : (i : ℕ) < (p : ℕ)) :
    tripleMatrix (L := DeployedField) sampleQueries baseProbeTriple p i = 0 := by
  rw [baseProbe_tripleMatrix_apply,
    kernelShift_coeff_zero_of_gt sampleQueries (by omega) (by omega)]

/-- The base probe matrix has determinant one. -/
theorem baseProbe_tripleMatrix_det :
    (tripleMatrix (L := DeployedField) sampleQueries baseProbeTriple).det = 1 := by
  rw [Matrix.det_fin_three, baseProbe_tripleMatrix_diag 0,
    baseProbe_tripleMatrix_diag 1, baseProbe_tripleMatrix_diag 2,
    baseProbe_tripleMatrix_lower 1 0 (by norm_num),
    baseProbe_tripleMatrix_lower 2 0 (by norm_num),
    baseProbe_tripleMatrix_lower 2 1 (by norm_num)]
  ring

/-- The base-field probe triple covers the scalar-extended kernel (which here
is just the base kernel). -/
theorem baseProbe_terminal_coverage :
    EqTerminalTripleCoversDeployedKernel (L := DeployedField) sampleQueries
      (fun _ => 1) baseProbeTriple :=
  eqTerminalTripleCovers_of_tripleMatrix_isUnit sampleQueries _ baseProbeTriple
    (by rw [baseProbe_tripleMatrix_det]; exact isUnit_one)

/-- At least one concrete mathematical public schedule satisfies the exact
base-source reference predicate.  This proves non-vacuity only; the fixed
coordinate-probe model is not the deployed eq-side MLE triple. -/
theorem baseProbePublicSchedule_exactTerminalRankPredicate :
    ExactTerminalRankPredicate unitWeightModel baseProbeTerminalModel
      baseProbePublicSchedule := by
  intro t
  obtain ⟨c, hsum, hquery, hterminal⟩ := baseProbe_terminal_coverage t
  refine ⟨c, hsum, ?_, ?_⟩
  · change (deployedFibreRectangularEval sampleQueries (fun _ => 1)).mulVec c = 0
    simpa [extendedFibreEval] using hquery
  · simpa [baseProbePublicSchedule, baseProbeTerminalModel] using hterminal

/-! ## Axiom audit -/

#print axioms exactTerminalRankPredicate_iff
#print axioms liftBaseCoins_self
#print axioms accepted_implies_terminal_coverage
#print axioms exactTerminalRankPredicate_public_ext
#print axioms allZero_exactTerminalRankPredicate_rejected
#print axioms allZero_reserved_conversion_counterexample_retained
#print axioms baseProbePublicSchedule_q18_injective
#print axioms baseProbe_tripleMatrix_apply
#print axioms baseProbe_tripleMatrix_diag
#print axioms baseProbe_tripleMatrix_lower
#print axioms baseProbe_tripleMatrix_det
#print axioms baseProbe_terminal_coverage
#print axioms baseProbePublicSchedule_exactTerminalRankPredicate

end AspisV5ComponentATerminalRankPredicate
