import Coordinates.Funs
import AspisFormal.CircleGroupOrder

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

/-!
# Exact values of the release coordinate windows

The production domain-19 coordinate path reconstructs a circle point from a
256-entry low window and a 512-entry high window emitted by `aspis-core`'s
build script.  This file checks those literal generated arrays in Lean and
connects every entry to the deployed circle generator.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriCoordinateTableSemantics

open AspisCircleGroupOrder

namespace Coordinate
open V5FriCoordinateAdapter

abbrev M31 := aspis_core.field.M31
abbrev Point := aspis_core.circle_fri.BaseCirclePoint

end Coordinate

def m31Value (value : Coordinate.M31) : ZMod P := value.val

def pointValue (point : Coordinate.Point) : ZMod P × ZMod P :=
  (m31Value point.x, m31Value point.y)

def tablePoint {N : Std.Usize}
    (table : Array (Array Std.U32 2#usize) N)
    (index : Fin N.val) : ZMod P × ZMod P :=
  let entry := table.val[index.val]!
  (entry.val[0]!.val, entry.val[1]!.val)

/- Computing `g ^ (2^k)` through the ordinary `Pow` recursion would take
billions of reductions for the largest table exponent.  The build script and
the mathematical development both use repeated squaring, so the closed table
checks below use the same logarithmic spelling. -/
def generatorPowTwo (log : Nat) : C :=
  (fun point : C => point ^ 2)^[log] g

def lowBase : C := generatorPowTwo 11
def lowStep : C := generatorPowTwo 13
def highStep : C := generatorPowTwo 21

theorem generatorPowTwo_eq (log : Nat) :
    generatorPowTwo log = g ^ (2 ^ log) := by
  exact sq_iterate log g

set_option pp.universes false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 50000000 in
theorem low_window_literals :
    ∀ index : Fin 256,
      tablePoint
          V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW
          index =
        (lowBase * lowStep ^ (index : Nat)).1 := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 80000000 in
theorem high_window_literals :
    ∀ index : Fin 512,
      tablePoint
          V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
          index =
        (highStep ^ (index : Nat)).1 := by
  decide

theorem low_window_exact (index : Fin 256) :
    tablePoint
        V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW
        index =
      (g ^ (2 ^ 11 + 2 ^ 13 * (index : Nat))).1 := by
  rw [low_window_literals index]
  apply congrArg Subtype.val
  unfold lowBase lowStep
  rw [generatorPowTwo_eq, generatorPowTwo_eq, ← pow_mul, ← pow_add]

theorem high_window_exact (index : Fin 512) :
    tablePoint
        V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
        index =
      (g ^ (2 ^ 21 * (index : Nat))).1 := by
  rw [high_window_literals index]
  apply congrArg Subtype.val
  unfold highStep
  rw [generatorPowTwo_eq, ← pow_mul]

#print axioms low_window_exact
#print axioms high_window_exact

end AspisV5FriCoordinateTableSemantics
