import V7K13FoldResidual.Funs

/-!
# Literal Tag-73 shifted residual source trace

The production helper is executable evidence for the shifted polynomial
shape.  It first evaluates the frozen V6 residual and then multiplies that
result by rho.  This theorem exposes those two same-run calls; it neither
assumes nor concludes that the residual is zero.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

open Aeneas Aeneas.Std Result ControlFlow Error
open V7K13FoldResidualGenerated

namespace AspisV7K13ShiftedResidualTrace

abbrev RawQM31 := field.QM31

structure ShiftedResidualSourceTrace
    (expected authenticated : Array RawQM31 16#usize)
    (rho shiftedResidual : RawQM31) : Type where
  baseResidual : RawQM31
  baseResidualSuccess :
    v6_query_batch.v6_final256_query_batch_residual expected authenticated rho =
      ok baseResidual
  shiftedMultiplySuccess :
    field.QM31.mul rho baseResidual = ok shiftedResidual

theorem successful_shifted_residual_exposes_exact_factorization
    (expected authenticated : Array RawQM31 16#usize)
    (rho shiftedResidual : RawQM31)
    (success :
      v6_query_batch.v7_final256_query_batch_shifted_residual expected
        authenticated rho = ok shiftedResidual) :
    Nonempty (ShiftedResidualSourceTrace expected authenticated rho
      shiftedResidual) := by
  unfold v6_query_batch.v7_final256_query_batch_shifted_residual at success
  cases hbase : v6_query_batch.v6_final256_query_batch_residual expected
      authenticated rho <;> simp [hbase] at success
  rename_i baseResidual
  cases hmul : field.QM31.mul rho baseResidual <;> simp [hmul] at success
  rename_i shiftedCandidate
  cases success
  exact ⟨{
    baseResidual := baseResidual
    baseResidualSuccess := hbase
    shiftedMultiplySuccess := hmul }⟩

#print axioms successful_shifted_residual_exposes_exact_factorization

end AspisV7K13ShiftedResidualTrace
