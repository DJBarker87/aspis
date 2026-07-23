import RuntimeSchedule
import AspisFormal.V5ComponentCDownstreamDeployed

/-!
# Source-authentic Component-C runtime schedule packaging

The generated Rust query derivation returns the three runtime-sized later-query
vectors.  This file packages those exact vectors into the maintained
`DeployedRuntimeSchedule` record.  In particular, the three count equalities
which were previously bundled into the downstream executable-correspondence
premise are definitional consequences of the generated output.

This file does not claim that the relation and FRI arithmetic implemented in
Rust equals the maintained evaluator; that is the remaining, separately named
arithmetic interface.
-/

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeScheduleProof

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCConcreteDownstream
open AspisV5ComponentCDownstreamDeployed

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

abbrev QueryIndices :=
  aspis_core.circle_line_merkle.CircleLineQueryIndices

abbrev later1 (indices : QueryIndices) : alloc.vec.Vec Std.U32 :=
  indices.later[0]

abbrev later2 (indices : QueryIndices) : alloc.vec.Vec Std.U32 :=
  indices.later[1]

abbrev later3 (indices : QueryIndices) : alloc.vec.Vec Std.U32 :=
  indices.later[2]

/-- Exactly the range facts needed to reinterpret the generated `u32` query
vectors as the three maintained finite fibre maps.  These are representation
bounds, not an evaluator-faithfulness premise. -/
def GeneratedLaterFibresInRange (indices : QueryIndices) : Prop :=
  (forall i : Fin (later1 indices).length,
    ((later1 indices).val[i.val]).val < layer2Symbols) /\
  (forall i : Fin (later2 indices).length,
    ((later2 indices).val[i.val]).val < layer3Symbols) /\
  (forall i : Fin (later3 indices).length,
    ((later3 indices).val[i.val]).val < layer4Symbols)

/-- Replace only the transcript-derived later-query fields of a supplied
arithmetic schedule.  Every later count and every ordered fibre is read
directly from the source-authentic generated Rust result. -/
def withGeneratedLaterFibres
    (base : DeployedRuntimeSchedule F K)
    (indices : QueryIndices)
    (hrange : GeneratedLaterFibresInRange indices) :
    DeployedRuntimeSchedule F K where
  alpha := base.alpha
  ood0 := base.ood0
  ood1 := base.ood1
  ood2 := base.ood2
  ood3 := base.ood3
  poly0 := base.poly0
  poly1 := base.poly1
  poly2 := base.poly2
  poly3 := base.poly3
  circleInv2x := base.circleInv2x
  circleInv2y := base.circleInv2y
  line1Inverse := base.line1Inverse
  line2Inverse := base.line2Inverse
  line3Inverse := base.line3Inverse
  later1Count := (later1 indices).length
  later2Count := (later2 indices).length
  later3Count := (later3 indices).length
  later1Fibre := fun i =>
    Fin.mk ((later1 indices).val[i.val]).val (hrange.1 i)
  later2Fibre := fun i =>
    Fin.mk ((later2 indices).val[i.val]).val (hrange.2.1 i)
  later3Fibre := fun i =>
    Fin.mk ((later3 indices).val[i.val]).val (hrange.2.2 i)
  finalX := base.finalX

@[simp] theorem withGeneratedLaterFibres_later1Count
    (base : DeployedRuntimeSchedule F K) (indices : QueryIndices)
    (hrange : GeneratedLaterFibresInRange indices) :
    (withGeneratedLaterFibres base indices hrange).later1Count =
      (later1 indices).length := rfl

@[simp] theorem withGeneratedLaterFibres_later2Count
    (base : DeployedRuntimeSchedule F K) (indices : QueryIndices)
    (hrange : GeneratedLaterFibresInRange indices) :
    (withGeneratedLaterFibres base indices hrange).later2Count =
      (later2 indices).length := rfl

@[simp] theorem withGeneratedLaterFibres_later3Count
    (base : DeployedRuntimeSchedule F K) (indices : QueryIndices)
    (hrange : GeneratedLaterFibresInRange indices) :
    (withGeneratedLaterFibres base indices hrange).later3Count =
      (later3 indices).length := rfl

@[simp] theorem withGeneratedLaterFibres_later1Fibre
    (base : DeployedRuntimeSchedule F K) (indices : QueryIndices)
    (hrange : GeneratedLaterFibresInRange indices)
    (i : Fin (later1 indices).length) :
    ((withGeneratedLaterFibres base indices hrange).later1Fibre i).val =
      ((later1 indices).val[i.val]).val := rfl

@[simp] theorem withGeneratedLaterFibres_later2Fibre
    (base : DeployedRuntimeSchedule F K) (indices : QueryIndices)
    (hrange : GeneratedLaterFibresInRange indices)
    (i : Fin (later2 indices).length) :
    ((withGeneratedLaterFibres base indices hrange).later2Fibre i).val =
      ((later2 indices).val[i.val]).val := rfl

@[simp] theorem withGeneratedLaterFibres_later3Fibre
    (base : DeployedRuntimeSchedule F K) (indices : QueryIndices)
    (hrange : GeneratedLaterFibresInRange indices)
    (i : Fin (later3 indices).length) :
    ((withGeneratedLaterFibres base indices hrange).later3Fibre i).val =
      ((later3 indices).val[i.val]).val := rfl

/-- On every successful execution of the generated Rust function, its three
returned vectors determine a maintained schedule with exactly the same counts
and order.  No separate count-correspondence premise is used. -/
theorem generated_success_packages_exact_schedule
    (queries : Slice Std.U32) (queryCount : Std.Usize)
    (indices : QueryIndices)
    (hrun :
      aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
          queries queryCount = ok (core.result.Result.Ok indices))
    (base : DeployedRuntimeSchedule F K)
    (hrange : GeneratedLaterFibresInRange indices) :
    let rt := withGeneratedLaterFibres base indices hrange
    aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
        queries queryCount = ok (core.result.Result.Ok indices) /\
      (alloc.vec.Vec.len (later1 indices)).val = rt.later1Count /\
      (alloc.vec.Vec.len (later2 indices)).val = rt.later2Count /\
      (alloc.vec.Vec.len (later3 indices)).val = rt.later3Count /\
      (forall i, (rt.later1Fibre i).val =
        ((later1 indices).val[i.val]).val) /\
      (forall i, (rt.later2Fibre i).val =
        ((later2 indices).val[i.val]).val) /\
      (forall i, (rt.later3Fibre i).val =
        ((later3 indices).val[i.val]).val) := by
  dsimp only
  refine ⟨hrun, ?_⟩
  simp

/-- The remaining executable interface after source-authentic schedule
packaging: only equality of the Rust relation/fold evaluator with the
maintained evaluator. -/
def RustRuntimeArithmeticCorrespondence
    (rt : DeployedRuntimeSchedule F K)
    (encodeFree : FreeCoordinateVector K →ₗ[K] CWord K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (rustEvaluate :
      FreeCoordinateVector K → Fin (fRows (decodeFriSchedule rt)) → K) : Prop :=
  RustDownstreamEvaluatorEqualsDeployed rt encodeFree enc rustEvaluate

#print axioms withGeneratedLaterFibres_later1Count
#print axioms withGeneratedLaterFibres_later2Count
#print axioms withGeneratedLaterFibres_later3Count
#print axioms withGeneratedLaterFibres_later1Fibre
#print axioms withGeneratedLaterFibres_later2Fibre
#print axioms withGeneratedLaterFibres_later3Fibre
#print axioms generated_success_packages_exact_schedule

end aspis_prover.ComponentCRuntimeScheduleProof
