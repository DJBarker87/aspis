import RuntimeGeneratedRelationSchedule
import RuntimeMaintainedRoundSelectors

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeGeneratedRoundSelectorsCurrent

open aspis_prover
open AspisV5ComponentCDownstreamDeployed
open AspisV5ComponentCRelationRowLinearity
open ComponentCRuntimeCoefficientFoldCorrespondence
open ComponentCRuntimeGeneratedRelationSchedule
open ComponentCRuntimeMaterializedRelationArithmetic

abbrev RawQM31 := aspis_core.field.QM31
abbrev BaseField := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev ExtensionField := AspisV5ComponentCQM31TowerExact.QM31Exact

def generatedOod0Weights (tables : FourRoundGeneratedTables) :
    Fin 2 → Fin 1024 → ExtensionField := fun sample =>
  exactSliceVector 1024
    (alloc.vec.Vec.deref (oodPairTable tables.ood0 sample))

def generatedOod1Weights (tables : FourRoundGeneratedTables) :
    Fin 2 → Fin 256 → ExtensionField := fun sample =>
  exactSliceVector 256
    (alloc.vec.Vec.deref (oodPairTable tables.ood1 sample))

def generatedOod2Weights (tables : FourRoundGeneratedTables) :
    Fin 2 → Fin 64 → ExtensionField := fun sample =>
  exactSliceVector 64
    (alloc.vec.Vec.deref (oodPairTable tables.ood2 sample))

theorem generatedOod0Weights_eq (tables : FourRoundGeneratedTables)
    (sample : Fin 2) : generatedOod0Weights tables sample =
      exactSliceVector 1024
        (alloc.vec.Vec.deref (oodPairTable tables.ood0 sample)) := rfl

theorem generatedOod1Weights_eq (tables : FourRoundGeneratedTables)
    (sample : Fin 2) : generatedOod1Weights tables sample =
      exactSliceVector 256
        (alloc.vec.Vec.deref (oodPairTable tables.ood1 sample)) := rfl

theorem generatedOod2Weights_eq (tables : FourRoundGeneratedTables)
    (sample : Fin 2) : generatedOod2Weights tables sample =
      exactSliceVector 64
        (alloc.vec.Vec.deref (oodPairTable tables.ood2 sample)) := rfl

attribute [irreducible] generatedOod0Weights generatedOod1Weights generatedOod2Weights

def generatedRelationSchedule
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables) : FixedRelationSchedule ExtensionField where
  alpha := base.alpha
  ood0 := generatedOod0Weights tables
  ood1 := generatedOod1Weights tables
  ood2 := generatedOod2Weights tables
  ood3 := fun sample => exactSliceVector 16
    (alloc.vec.Vec.deref (oodPairTable tables.ood3 sample))
  poly0 := exactSliceVector 1024 (alloc.vec.Vec.deref tables.polynomial0.table)
  poly1 := exactSliceVector 256 (alloc.vec.Vec.deref tables.polynomial1.table)
  poly2 := exactSliceVector 64 (alloc.vec.Vec.deref tables.polynomial2.table)
  poly3 := exactSliceVector 16 (alloc.vec.Vec.deref tables.polynomial3.table)

theorem generated_round_ood0_scalar
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients ExtensionField)
    (sample : Fin 2) :
    roundOodRows (generatedRelationSchedule base tables) 0 c sample =
      dotLinear (exactSliceVector 1024
        (alloc.vec.Vec.deref (oodPairTable tables.ood0 sample))) c := by
  let exactWeights : Fin 2 → Fin 1024 → ExtensionField := fun s =>
    exactSliceVector 1024
      (alloc.vec.Vec.deref (oodPairTable tables.ood0 s))
  have hweights : generatedOod0Weights tables = exactWeights := by
    funext s
    exact generatedOod0Weights_eq tables s
  have hschedule :
      (generatedRelationSchedule base tables).ood0 =
        generatedOod0Weights tables := rfl
  have hmaps : roundOodRows (generatedRelationSchedule base tables) 0 =
      LinearMap.pi (fun s => dotLinear (exactWeights s)) := by
    calc
      roundOodRows (generatedRelationSchedule base tables) 0 =
          ood0Rows (generatedRelationSchedule base tables) :=
        roundOodRows_zero_map _
      _ = LinearMap.pi (fun s => dotLinear
          ((generatedRelationSchedule base tables).ood0 s)) :=
        ood0Rows_body_map _
      _ = LinearMap.pi (fun s => dotLinear (generatedOod0Weights tables s)) :=
        congrArg (fun weights => LinearMap.pi (fun s => dotLinear (weights s)))
          hschedule
      _ = LinearMap.pi (fun s => dotLinear (exactWeights s)) :=
        congrArg (fun weights => LinearMap.pi (fun s => dotLinear (weights s)))
          hweights
  calc
    roundOodRows (generatedRelationSchedule base tables) 0 c sample =
        (LinearMap.pi (fun s => dotLinear (exactWeights s)) c) sample :=
      congrArg (fun m => m c sample) hmaps
    _ = dotLinear (exactWeights sample) c :=
      LinearMap.pi_apply (fun s => dotLinear (exactWeights s)) c sample
    _ = dotLinear (exactSliceVector 1024
        (alloc.vec.Vec.deref (oodPairTable tables.ood0 sample))) c := rfl

theorem generated_round_ood1_scalar
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients ExtensionField)
    (sample : Fin 2) :
    roundOodRows (generatedRelationSchedule base tables) 1 c sample =
      dotLinear (exactSliceVector 256
        (alloc.vec.Vec.deref (oodPairTable tables.ood1 sample)))
        (round1Coefficients (generatedRelationSchedule base tables) c) := by
  rw [roundOodRows_one]
  exact dotLinear_transport_256 (generatedOod1Weights_eq tables sample) _

theorem generated_round_ood2_scalar
    (base : DeployedRuntimeSchedule BaseField ExtensionField)
    (tables : FourRoundGeneratedTables)
    (c : AspisV5ComponentCConcreteFoldLinearity.Coefficients ExtensionField)
    (sample : Fin 2) :
    roundOodRows (generatedRelationSchedule base tables) 2 c sample =
      dotLinear (exactSliceVector 64
        (alloc.vec.Vec.deref (oodPairTable tables.ood2 sample)))
        (round2Coefficients (generatedRelationSchedule base tables) c) := by
  rw [roundOodRows_two]
  exact dotLinear_transport_64 (generatedOod2Weights_eq tables sample) _

#print axioms generated_round_ood0_scalar
#print axioms generated_round_ood1_scalar
#print axioms generated_round_ood2_scalar

end aspis_prover.ComponentCRuntimeGeneratedRoundSelectorsCurrent
