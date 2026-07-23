import GoodMatricesCurrent.SourceExtractedField
import ComponentBInstallerShared

#print AuthenticFieldPreparedMul.field.PreparedQm31Multiplier
#print AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul
#print AuthenticFieldPreparedMul.field.CM31
#print AuthenticFieldPreparedMul.field.QM31
#print AuthenticFieldPreparedMul.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
#print AuthenticFieldPreparedMul.field.CM31.add
#print AuthenticFieldPreparedMul.field.CM31.sub
#print AuthenticFieldPreparedMul.field.M31.add
#print AuthenticFieldPreparedMul.field.M31.sub
#print AuthenticFieldPreparedMul.field.M31.mul
#print AuthenticFieldPreparedMul.field.mul_by_r
#print AuthenticFieldPow.field.QM31.mul
#print AspisCoreAdditive.field.QM31.sub
#print aspis_core.field.PreparedQm31Multiplier.mul
#check AspisV5ComponentCQM31RustFormulaSeam.exact_qm31_mul
#check GoodMatricesCurrent.SourceExtractedField.authentic_reduce_u64_word_spec

example (x y : Std.U32) :
    AuthenticFieldPreparedMul.field.M31.add x y =
      aspis_core.field.M31.add x y := by rfl
example (x y : Std.U32) :
    AuthenticFieldPreparedMul.field.M31.sub x y =
      aspis_core.field.M31.sub x y := by rfl
example (x y : Std.U32) :
    AuthenticFieldPreparedMul.field.M31.mul x y =
      aspis_core.field.M31.mul x y := by rfl
example (x : AuthenticFieldPreparedMul.field.CM31) :
    AuthenticFieldPreparedMul.field.mul_by_r x =
      AuthenticFieldPow.field.mul_by_r { a := x.a, b := x.b } := by rfl
