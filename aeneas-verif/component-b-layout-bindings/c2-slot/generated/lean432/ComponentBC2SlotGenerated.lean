-- Lean-4.32 replay of the exact Aeneas function bodies in
-- `generated/raw/ComponentBC2Slot.lean`.  The source types are reused from
-- the independently authenticated Component-B layout extraction so the same
-- Rust lane is not represented by a second Lean structure.
import ComponentBLayoutBindingsGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBC2SlotGenerated

open ComponentBGenerated

abbrev QM31 := ComponentBGenerated.aspis_core.field.QM31
abbrev Lane :=
  ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane

/-- [aspis_prover::v5_mask::V5_TRACE_ROWS]
    Source: `crates/aspis-prover/src/v5_mask.rs`, line 146. -/
def V5_TRACE_ROWS : Std.Usize := 1024#usize

/-- Exact Aeneas loop body for
`aspis_prover::v5_mask::spend_messages::component_b_message_values`. -/
def component_b_message_values_loop.body
    (componentB : Lane) (values : alloc.vec.Vec QM31) (row : Std.Usize) :
    Result (ControlFlow ((alloc.vec.Vec QM31) × Std.Usize)
      (alloc.vec.Vec QM31)) := do
  if row < V5_TRACE_ROWS then
    let value ← Array.index_usize componentB.values row
    let values ← alloc.vec.Vec.push values value
    let row ← lift (Std.Usize.wrapping_add row 1#usize)
    ok (cont (values, row))
  else
    ok (done values)

/-- Exact Aeneas loop for the source indexed copy. -/
def component_b_message_values_loop
    (componentB : Lane) (values : alloc.vec.Vec QM31)
    (row : Std.Usize) : Result (alloc.vec.Vec QM31) := do
  loop
    (fun (values, row) ↦
      component_b_message_values_loop.body componentB values row)
    (values, row)

/-- Exact Aeneas top-level definition for the source indexed copy. -/
def component_b_message_values (componentB : Lane) :
    Result (alloc.vec.Vec QM31) := do
  let values := alloc.vec.Vec.with_capacity QM31 V5_TRACE_ROWS
  component_b_message_values_loop componentB values 0#usize

/-- Exact Aeneas definition for the source three-lane constructor. -/
def assemble_v5_c2_messages
    (hcopy componentB componentC : alloc.vec.Vec QM31) :
    Result (Array (alloc.vec.Vec QM31) 3#usize) :=
  ok (Array.make 3#usize [hcopy, componentB, componentC])

end ComponentBC2SlotGenerated
