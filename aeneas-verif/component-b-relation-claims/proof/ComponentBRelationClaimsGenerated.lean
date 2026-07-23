-- The definitions below are the exact Aeneas output for the production
-- Component-B relation-claim helper.  The common field and MLE declarations
-- are imported from their separately authenticated owning-source extraction;
-- `generated/ComponentBRelationClaims.lean` retains the complete raw output.
import MultilinearEvalWrappersTransparent

open Aeneas Aeneas.Std Result ControlFlow Error

namespace aspis_prover

/-- [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Source: 'crates/aspis-core/src/field.rs', lines 715:4-715:24
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::QM31}::ZERO"]
def aspis_core.field.QM31.ZERO : aspis_core.field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_prover::v5_mask::split_layer_zero::V5_RELATION_POINT_CLAIMS]
    Source: 'crates/aspis-prover/src/v5_split_layer_zero.rs', lines 54:0-54:46
    Visibility: public -/
@[global_simps, irreducible]
def v5_mask.split_layer_zero.V5_RELATION_POINT_CLAIMS : Std.Usize := 3#usize

/-- [aspis_prover::v5_mask::split_layer_zero::evaluate_component_b_relation_claims]: loop 0:
    Source: 'crates/aspis-prover/src/v5_split_layer_zero.rs', lines 190:4-193:5 -/
@[rust_loop]
def v5_mask.split_layer_zero.evaluate_component_b_relation_claims_loop
  (terminal_covector : Slice aspis_core.field.QM31)
  (message : alloc.vec.Vec aspis_core.field.QM31)
  (terminal : aspis_core.field.QM31) (row : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let i := alloc.vec.Vec.len message
  if row < i
  then
    let i1 := Slice.len terminal_covector
    if row < i1
    then
      let q ← Slice.index_usize terminal_covector row
      let q1 ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          aspis_core.field.QM31) message row
      let q2 ← aspis_core.field.QM31.mul q q1
      let terminal1 ← aspis_core.field.QM31.add terminal q2
      let row1 ← lift (Std.Usize.wrapping_add row 1#usize)
      v5_mask.split_layer_zero.evaluate_component_b_relation_claims_loop
        terminal_covector message terminal1 row1
    else ok terminal
  else ok terminal
partial_fixpoint

/-- [aspis_prover::v5_mask::split_layer_zero::evaluate_component_b_relation_claims]:
    Source: 'crates/aspis-prover/src/v5_split_layer_zero.rs', lines 177:0-196:1 -/
def v5_mask.split_layer_zero.evaluate_component_b_relation_claims
  (c2_messages : Array (alloc.vec.Vec aspis_core.field.QM31) 3#usize)
  (points : Array (Array aspis_core.field.QM31 10#usize) 3#usize)
  (terminal_covector : Slice aspis_core.field.QM31) :
  Result (Array aspis_core.field.QM31 4#usize)
  := do
  let message ← Array.index_usize c2_messages 1#usize
  let claims := Array.repeat 4#usize aspis_core.field.QM31.ZERO
  let s := alloc.vec.Vec.deref message
  let a ← Array.index_usize points 0#usize
  let s1 ← lift (Array.to_slice a)
  let q ← multilinear_eval_extension s s1
  let claims1 ← Array.update claims 0#usize q
  let s2 := alloc.vec.Vec.deref message
  let a1 ← Array.index_usize points 1#usize
  let s3 ← lift (Array.to_slice a1)
  let q1 ← multilinear_eval_extension s2 s3
  let claims2 ← Array.update claims1 1#usize q1
  let s4 := alloc.vec.Vec.deref message
  let a2 ← Array.index_usize points 2#usize
  let s5 ← lift (Array.to_slice a2)
  let q2 ← multilinear_eval_extension s4 s5
  let claims3 ← Array.update claims2 2#usize q2
  let terminal ←
    v5_mask.split_layer_zero.evaluate_component_b_relation_claims_loop
      terminal_covector message aspis_core.field.QM31.ZERO 0#usize
  Array.update claims3 v5_mask.split_layer_zero.V5_RELATION_POINT_CLAIMS
    terminal

end aspis_prover
