import PoolV1RootHistoryLocation.Funs
import AspisFormal.Pool.RootHistoryV1
import Aeneas.Tactic.Step.Step

/-!
# Pool V1 root-history location source bridge

This theorem starts at the literal Charon/Aeneas translation of the production
Rust wrapper around `root_history_location` and identifies its successful
result with the frozen Pool V1 quotient/remainder model.
-/

set_option autoImplicit false

namespace PoolV1TreeHistorySourceBridge

open Aeneas Aeneas.Std Result
open PoolV1RootHistoryLocationGenerated

abbrev GeneratedLocation :=
  PoolV1RootHistoryLocationGenerated.aspis_statement.pool_v1.root_history.RootHistoryLocationV1

def toModelLocation (location : GeneratedLocation) :
    AspisPool.RootHistoryV1.Location :=
  { pageNumber := location.page_number.val
    slot := location.slot.val }

theorem production_root_history_location_source_exact
    (sequence : Std.U64) (out : GeneratedLocation)
    (run : production_root_history_location sequence = .ok out) :
    toModelLocation out = AspisPool.RootHistoryV1.location sequence.val := by
  have hspec :
      production_root_history_location sequence
        ⦃ result =>
          toModelLocation result =
            AspisPool.RootHistoryV1.location sequence.val ⦄ := by
    unfold production_root_history_location
    unfold PoolV1RootHistoryLocationGenerated.aspis_statement.pool_v1.root_history.root_history_location
    unfold PoolV1RootHistoryLocationGenerated.aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_CAPACITY
    unfold PoolV1RootHistoryLocationGenerated.aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_CAPACITY_LOG2
    repeat' step
    all_goals simp_all [toModelLocation, AspisPool.RootHistoryV1.location,
      AspisPool.RootHistoryV1.pageCapacity]
    all_goals cases System.Platform.numBits_eq <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, *]
    all_goals omega
  rw [run] at hspec
  exact hspec

#print axioms production_root_history_location_source_exact

end PoolV1TreeHistorySourceBridge
