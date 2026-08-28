import PoolV1CopyLaneBooleanGenerated.Funs
import AspisFormal.Pool.NativePaymentCopyLaneBooleanRefinementV1

/-!
# Generated native Pool V1 Boolean Copy-lane root

This module is the deliberately small adapter between the pinned Aeneas root
and `ExtractedRustBooleanCopyLane`.  It does not interpret the field or replace
any generated loop/table with a handwritten evaluator.  In particular,
`generatedEvaluate` calls the extracted public wrapper, whose successful
branches call the extracted private production `copy_lane` root.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisPoolV1CopyLaneBooleanRoot

open PoolV1CopyLaneBooleanGenerated
open AspisPool.NativePaymentCopyLaneBooleanRefinementV1
open AspisPool.NativePaymentCompiledActiveMaskV1

abbrev RootQM31 := PoolV1CopyLaneBooleanGenerated.aspis_core.field.QM31

def array16OfFn (values : Fin 16 → RootQM31) : Array RootQM31 16#usize :=
  Array.make 16#usize (List.ofFn values)

@[simp] theorem array16OfFn_get (values : Fin 16 → RootQM31)
    (index : Fin 16) :
    (array16OfFn values).val[index.val]'(by
      rw [(array16OfFn values).property]
      exact index.isLt) = values index := by
  fin_cases index <;> rfl

def selectedU16 (selected : Fin 1024) : Std.U16 :=
  Std.U16.ofNatCore selected.val (by
    change selected.val < 65536
    omega)

@[simp] theorem selectedU16_val (selected : Fin 1024) :
    (selectedU16 selected).val = selected.val := by
  simp [selectedU16]

def variantU8 : NativePaymentVariantV1 → Std.U8
  | .privateTransfer => 0#u8
  | .withdrawal => 1#u8

def successfulOption {T : Type*} : Result (Option T) → Option T
  | .ok output => output
  | .fail _ => none
  | .div => none

def generatedEvaluate
    (variant : NativePaymentVariantV1) (selected : Fin 1024)
    (openings : Fin 16 → RootQM31) (h1 lambda chi : RootQM31) :
    Option (RootQM31 × RootQM31) :=
  successfulOption
    (pool_v1.payment_semantic_terminal.pool_v1_payment_copy_lane_boolean_extraction_v1
      (variantU8 variant) (selectedU16 selected) (array16OfFn openings)
      h1 lambda chi)

def generatedRustBooleanCopyLane : ExtractedRustBooleanCopyLane RootQM31 where
  evaluate := generatedEvaluate

/-- Successful adapter evaluation is exactly successful execution of the
pinned generated wrapper.  This keeps all later inversion on the authenticated
Charon/Aeneas term rather than on a parallel model. -/
theorem generatedEvaluate_success_iff
    (variant : NativePaymentVariantV1) (selected : Fin 1024)
    (openings : Fin 16 → RootQM31) (h1 lambda chi : RootQM31)
    (output : RootQM31 × RootQM31) :
    generatedEvaluate variant selected openings h1 lambda chi = some output ↔
      pool_v1.payment_semantic_terminal.pool_v1_payment_copy_lane_boolean_extraction_v1
        (variantU8 variant) (selectedU16 selected) (array16OfFn openings)
          h1 lambda chi = .ok (some output) := by
  unfold generatedEvaluate successfulOption
  generalize call :
    pool_v1.payment_semantic_terminal.pool_v1_payment_copy_lane_boolean_extraction_v1
      (variantU8 variant) (selectedU16 selected) (array16OfFn openings)
        h1 lambda chi = result
  cases result <;> simp_all [successfulOption]

#print axioms generatedEvaluate_success_iff

end AspisPoolV1CopyLaneBooleanRoot
