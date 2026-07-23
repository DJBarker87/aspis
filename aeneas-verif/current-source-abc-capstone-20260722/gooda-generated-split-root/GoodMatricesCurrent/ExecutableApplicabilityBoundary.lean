import GoodMatricesCurrent.ConcreteProbeTerminalMatrixCapstone

/-!
# Component-A executable applicability boundary

This file joins the source-extracted `good_matrices` output to the maintained
`selectedTerminalMinor` entry-by-entry at the one schedule for which the
current extraction is specialized.  The separately kernel-checked runtime
order graph closes stored-q18 normalization, slot order, and C1 packer order,
but its generated environment is intentionally not merged here: it and the
GoodA extraction contain overlapping generated Rust declarations.

The current extracted graph does not contain `candidate_is_good`,
`m31_matrix_nonsingular`, or a `good_matrices` theorem parameterized by an
arbitrary runtime schedule.  The final theorem is therefore a hostile
countermodel: agreement at the concrete probe cannot establish the universal
`VerifierEnforcesGoodA` relation.  In particular, a predicate accepting every
schedule agrees at the good concrete probe but wrongly accepts the maintained
all-zero regression schedule.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open Matrix Polynomial

namespace GoodMatricesCurrent.ExecutableApplicabilityBoundary

open aspis_verifier
open AspisCircleDiscreteAvailability
open AspisV5AtomicComponentACorrespondence
open AspisV5ComponentARankCompletion
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentADeployedTerminalApplicability.ConcreteProbeWitness
open AspisV5ComponentADeployedTerminalApplicability.UnmetDeployment
open AspisV5ComponentATerminalRankPredicate
open GoodMatricesCurrent.ConcreteProbeTerminalMatrixCapstone
open GoodMatricesCurrent.ProbeTerminalMatrixAssembly
open GoodMatricesCurrent.SourceExtractedGoodAMatrixOutput
open GoodMatricesCurrent.ProbeGeneratedConcrete

abbrev Base := AspisV5ComponentADeployedTerminalApplicability.Base
abbrev Tower := AspisV5ComponentADeployedTerminalApplicability.Tower

/-- The exact source-extracted A matrix and the maintained concrete minor are
the same matrix after the explicit point/limb ordinal conversion.  Unlike the
older side-by-side capstone, this theorem states the direct entry equality. -/
theorem generated_a_projection_matches_maintained_concrete_minor :
    ∃ finalA finalB,
      v5_cu_probe.good_gate_probe.good_matrices kernel point =
        .ok (finalA, finalB) ∧
      ∀ row column : TerminalLimb,
        aMatrixToExact finalA (terminalLimbOrdinal row)
            (terminalLimbOrdinal column) =
          selectedTerminalMinor concreteSchedule row column := by
  obtain ⟨finalA, finalB, hcall, hmatrix⟩ :=
    generated_good_matrices_a_projection_eq_printed
  refine ⟨finalA, finalB, hcall, ?_⟩
  intro row column
  rw [hmatrix, selectedTerminalMinor_entry_eq_assembled,
    assembledTerminalMatrixFin_eq_printed]

/-- The first exact entry of the source-extracted matrix join.  This is the
`(terminal 0, limb 0)` row and column, hence ordinal `(0, 0)` in the Rust
12-by-12 M31 matrix. -/
theorem generated_first_entry_matches_maintained_concrete_minor :
    ∃ finalA finalB,
      v5_cu_probe.good_gate_probe.good_matrices kernel point =
        .ok (finalA, finalB) ∧
      aMatrixToExact finalA 0 0 =
        selectedTerminalMinor concreteSchedule
          ((0, 0) : TerminalLimb) ((0, 0) : TerminalLimb) := by
  obtain ⟨finalA, finalB, hcall, hentries⟩ :=
    generated_a_projection_matches_maintained_concrete_minor
  refine ⟨finalA, finalB, hcall, ?_⟩
  simpa [terminalLimbOrdinal, terminalLimbIndex] using
    hentries ((0, 0) : TerminalLimb) ((0, 0) : TerminalLimb)

/-- The maintained concrete GoodA success reaches terminal coverage without
an additional Rust↔Lean premise.  The source-extracted matrix equality is the
separate theorem above; both remain deliberately specialized to the concrete
public probe rather than an arbitrary selected runtime schedule. -/
theorem concrete_maintained_gate_covers_deployed_kernel
    (weightModel : PublicWeightModel) :
    EqTerminalTripleCoversDeployedKernel concreteSchedule.q18
      (weightModel concreteSchedule.q18)
      (deployedTerminalModel concreteSchedule.point) :=
  goodA_implies_deployedTerminalCoverage weightModel concreteSchedule
    concreteProbe_goodA_unconditional

/-- Concrete hostile countermodel.  A verifier predicate can agree with the
source-extracted/maintained concrete success while failing the universal
executable GoodA relation at the retained all-zero schedule.  Consequently a
fixed probe theorem cannot discharge `VerifierEnforcesGoodA`. -/
theorem concrete_probe_agreement_does_not_imply_verifier_enforces_goodA :
    ∃ verifierAccepts : PublicTerminalSchedule Tower → Prop,
      verifierAccepts concreteSchedule ∧
      GoodA concreteSchedule ∧
      ¬ VerifierEnforcesGoodA verifierAccepts := by
  let verifierAccepts : PublicTerminalSchedule Tower → Prop := fun _ => True
  refine ⟨verifierAccepts, trivial, concreteProbe_goodA_unconditional, ?_⟩
  intro henforces
  have hbad : GoodA (allZeroSchedule naturalQ18) :=
    (henforces (allZeroSchedule naturalQ18)).mp trivial
  exact deployed_allZero_goodA_rejected naturalQ18 hbad

#print axioms generated_a_projection_matches_maintained_concrete_minor
#print axioms generated_first_entry_matches_maintained_concrete_minor
#print axioms concrete_maintained_gate_covers_deployed_kernel
#print axioms concrete_probe_agreement_does_not_imply_verifier_enforces_goodA

end GoodMatricesCurrent.ExecutableApplicabilityBoundary
