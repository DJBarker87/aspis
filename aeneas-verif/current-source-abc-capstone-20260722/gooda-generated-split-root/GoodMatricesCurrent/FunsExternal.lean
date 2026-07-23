-- Handwritten composition file for the Aeneas split output. Every external
-- is a transparent constructor or an adapter to an independently
-- source-extracted definition of the same current Rust field primitive.
import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import Aeneas.Data.Discriminant
import GoodMatricesCurrent.Types
import ComponentBInstallerShared

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

private abbrev LocalM31 := aspis_verifier.aspis_core.field.M31
private abbrev LocalCM31 := aspis_verifier.aspis_core.field.CM31
private abbrev LocalQM31 := aspis_verifier.aspis_core.field.QM31

private def toCurrentCM31 (value : LocalCM31) :
    _root_.aspis_core.field.CM31 :=
  { a := value.a, b := value.b }

private def fromCurrentCM31 (value : _root_.aspis_core.field.CM31) :
    LocalCM31 :=
  { a := value.a, b := value.b }

private def toCurrentQM31 (value : LocalQM31) :
    _root_.aspis_core.field.QM31 :=
  { c0 := toCurrentCM31 value.c0, c1 := toCurrentCM31 value.c1 }

private def fromCurrentQM31 (value : _root_.aspis_core.field.QM31) :
    LocalQM31 :=
  { c0 := fromCurrentCM31 value.c0, c1 := fromCurrentCM31 value.c1 }

private def localM31Zero : LocalM31 := 0#u32

private def localCM31Zero : LocalCM31 :=
  { a := localM31Zero, b := localM31Zero }

private def localQM31Zero : LocalQM31 :=
  { c0 := localCM31Zero, c1 := localCM31Zero }

def aspis_verifier.aspis_core.field.P : Result Std.U32 :=
  .ok _root_.aspis_core.field.P

def aspis_verifier.aspis_core.field.M31.ZERO : Result LocalM31 :=
  .ok _root_.aspis_core.field.M31.ZERO

def aspis_verifier.aspis_core.field.M31.add
    (left right : LocalM31) : Result LocalM31 :=
  _root_.aspis_core.field.M31.add left right

def aspis_verifier.aspis_core.field.M31.reduce_u64
    (value : Std.U64) : Result LocalM31 :=
  AuthenticFieldPow.field.reduce_u64 value

def aspis_verifier.aspis_core.field.M31.half
    (value : LocalM31) : Result LocalM31 :=
  _root_.aspis_core.field.M31.half value

def aspis_verifier.aspis_core.field.M31.is_zero
    (value : LocalM31) : Result Bool :=
  .ok (value = 0#u32)

def aspis_verifier.aspis_core.field.CM31.new
    (a b : LocalM31) : Result LocalCM31 :=
  .ok { a, b }

def aspis_verifier.aspis_core.field.CM31.from_m31
    (value : LocalM31) : Result LocalCM31 :=
  .ok { a := value, b := localM31Zero }

def aspis_verifier.aspis_core.field.PreparedQm31Multiplier.new
    (value : LocalQM31) :
    Result _root_.aspis_core.field.PreparedQm31Multiplier := do
  let c0sum ← aspis_verifier.aspis_core.field.M31.add value.c0.a value.c0.b
  let c1sum ← aspis_verifier.aspis_core.field.M31.add value.c1.a value.c1.b
  let c01a ← aspis_verifier.aspis_core.field.M31.add value.c0.a value.c1.a
  let c01b ← aspis_verifier.aspis_core.field.M31.add value.c0.b value.c1.b
  let c01sum ← aspis_verifier.aspis_core.field.M31.add c01a c01b
  .ok {
    components := Array.make 3#usize [
      Array.make 3#usize [value.c0.a, value.c0.b, c0sum],
      Array.make 3#usize [value.c1.a, value.c1.b, c1sum],
      Array.make 3#usize [c01a, c01b, c01sum]
    ]
  }

def aspis_verifier.aspis_core.field.PreparedQm31Multiplier.mul
    (prepared : _root_.aspis_core.field.PreparedQm31Multiplier)
    (rhs : LocalQM31) : Result LocalQM31 := do
  let value ← _root_.aspis_core.field.PreparedQm31Multiplier.mul
    prepared (toCurrentQM31 rhs)
  .ok (fromCurrentQM31 value)

def aspis_verifier.aspis_core.field.QM31.ZERO : Result LocalQM31 :=
  .ok localQM31Zero

def aspis_verifier.aspis_core.field.QM31.ONE : Result LocalQM31 :=
  .ok {
    c0 := { a := 1#u32, b := localM31Zero },
    c1 := localCM31Zero
  }

def aspis_verifier.aspis_core.field.QM31.from_cm31
    (value : LocalCM31) : Result LocalQM31 :=
  .ok { c0 := value, c1 := localCM31Zero }

def aspis_verifier.aspis_core.field.QM31.add
    (left right : LocalQM31) : Result LocalQM31 := do
  let value ← _root_.aspis_core.field.QM31.add
    (toCurrentQM31 left) (toCurrentQM31 right)
  .ok (fromCurrentQM31 value)

def aspis_verifier.aspis_core.field.QM31.sub
    (left right : LocalQM31) : Result LocalQM31 := do
  let value ← _root_.aspis_core.field.QM31.sub
    (toCurrentQM31 left) (toCurrentQM31 right)
  .ok (fromCurrentQM31 value)

def aspis_verifier.aspis_core.field.QM31.mul
    (left right : LocalQM31) : Result LocalQM31 := do
  let value ← _root_.aspis_core.field.QM31.mul
    (toCurrentQM31 left) (toCurrentQM31 right)
  .ok (fromCurrentQM31 value)

/- Public definitional projections for the structure-only current-field
   adapters above.  Each equation is reflexivity inside this module, where the
   private conversion helpers remain visible. -/
theorem aspis_verifier.aspis_core.field.PreparedQm31Multiplier.mul_eq_current
    (prepared : _root_.aspis_core.field.PreparedQm31Multiplier)
    (rhs : LocalQM31) :
    aspis_verifier.aspis_core.field.PreparedQm31Multiplier.mul prepared rhs =
      (do
        let value ← _root_.aspis_core.field.PreparedQm31Multiplier.mul
          prepared
          { c0 := { a := rhs.c0.a, b := rhs.c0.b },
            c1 := { a := rhs.c1.a, b := rhs.c1.b } }
        .ok ({
          c0 := { a := value.c0.a, b := value.c0.b },
          c1 := { a := value.c1.a, b := value.c1.b }
        } : LocalQM31)) := by
  rfl

theorem aspis_verifier.aspis_core.field.QM31.add_eq_current
    (left right : LocalQM31) :
    aspis_verifier.aspis_core.field.QM31.add left right =
      (do
        let value ← _root_.aspis_core.field.QM31.add
          { c0 := { a := left.c0.a, b := left.c0.b },
            c1 := { a := left.c1.a, b := left.c1.b } }
          { c0 := { a := right.c0.a, b := right.c0.b },
            c1 := { a := right.c1.a, b := right.c1.b } }
        .ok ({
          c0 := { a := value.c0.a, b := value.c0.b },
          c1 := { a := value.c1.a, b := value.c1.b }
        } : LocalQM31)) := by
  rfl

theorem aspis_verifier.aspis_core.field.QM31.sub_eq_current
    (left right : LocalQM31) :
    aspis_verifier.aspis_core.field.QM31.sub left right =
      (do
        let value ← _root_.aspis_core.field.QM31.sub
          { c0 := { a := left.c0.a, b := left.c0.b },
            c1 := { a := left.c1.a, b := left.c1.b } }
          { c0 := { a := right.c0.a, b := right.c0.b },
            c1 := { a := right.c1.a, b := right.c1.b } }
        .ok ({
          c0 := { a := value.c0.a, b := value.c0.b },
          c1 := { a := value.c1.a, b := value.c1.b }
        } : LocalQM31)) := by
  rfl

theorem aspis_verifier.aspis_core.field.QM31.mul_eq_current
    (left right : LocalQM31) :
    aspis_verifier.aspis_core.field.QM31.mul left right =
      (do
        let value ← _root_.aspis_core.field.QM31.mul
          { c0 := { a := left.c0.a, b := left.c0.b },
            c1 := { a := left.c1.a, b := left.c1.b } }
          { c0 := { a := right.c0.a, b := right.c0.b },
            c1 := { a := right.c1.a, b := right.c1.b } }
        .ok ({
          c0 := { a := value.c0.a, b := value.c0.b },
          c1 := { a := value.c1.a, b := value.c1.b }
        } : LocalQM31)) := by
  rfl
