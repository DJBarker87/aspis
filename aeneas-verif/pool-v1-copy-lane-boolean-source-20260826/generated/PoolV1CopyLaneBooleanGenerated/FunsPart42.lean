-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart41
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::copy_residual]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 319:0-337:1 -/
def pool_v1.payment_semantic_terminal.copy_residual
  (row : pool_v1.payment_semantic_terminal.CopyRowExtension)
  (helper : aspis_core.field.QM31) (chi : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let q ← Array.index_usize row.producer_values 0#usize
  let q1 ← aspis_core.field.QM31.sub chi q
  let q2 ← Array.index_usize row.producer_values 1#usize
  let q3 ← aspis_core.field.QM31.sub chi q2
  let q4 ← Array.index_usize row.consumer_values 0#usize
  let q5 ← aspis_core.field.QM31.sub chi q4
  let q6 ← Array.index_usize row.consumer_values 1#usize
  let q7 ← aspis_core.field.QM31.sub chi q6
  let q8 ← Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 0#usize
  let q9 ← Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 1#usize
  let producer_denominator ← aspis_core.field.QM31.mul q8 q9
  let q10 ← Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 2#usize
  let q11 ← Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 3#usize
  let consumer_denominator ← aspis_core.field.QM31.mul q10 q11
  let q12 ← Array.index_usize row.producer_weights 0#usize
  let q13 ← aspis_core.field.QM31.mul q12 q9
  let q14 ← Array.index_usize row.producer_weights 1#usize
  let q15 ← aspis_core.field.QM31.mul q14 q8
  let producer_numerator ← aspis_core.field.QM31.add q13 q15
  let q16 ← Array.index_usize row.consumer_weights 0#usize
  let q17 ← aspis_core.field.QM31.mul q16 q11
  let q18 ← Array.index_usize row.consumer_weights 1#usize
  let q19 ← aspis_core.field.QM31.mul q18 q10
  let consumer_numerator ← aspis_core.field.QM31.add q17 q19
  let q20 ← aspis_core.field.QM31.mul helper consumer_denominator
  let q21 ← aspis_core.field.QM31.add q20 consumer_numerator
  let q22 ← aspis_core.field.QM31.mul producer_denominator q21
  let q23 ← aspis_core.field.QM31.mul consumer_denominator producer_numerator
  aspis_core.field.QM31.sub q22 q23

end PoolV1CopyLaneBooleanGenerated
