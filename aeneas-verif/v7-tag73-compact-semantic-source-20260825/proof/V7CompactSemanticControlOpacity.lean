import V7CompactSemanticChallengeOpaqueNoDedup.Funs

open V7CompactSemanticFullGenerated

/- These definitions are source-transparent in the generated module.  The
control-only proof imports this module to keep child calls atomic while it
projects the literal loop/range/read schedule. -/
attribute [local irreducible]
  V7CompactSemanticFullGenerated.field.M31.reduce_u64
  V7CompactSemanticFullGenerated.field.CM31.new
  V7CompactSemanticFullGenerated.field.QM31.Insts.CoreCmpPartialEqQM31.eq
  V7CompactSemanticFullGenerated.field.PreparedQm31Multiplier.new
  V7CompactSemanticFullGenerated.field.PreparedQm31Multiplier.mul
  V7CompactSemanticFullGenerated.field.qm31_sum_products3
  V7CompactSemanticFullGenerated.field.QM31.add
  V7CompactSemanticFullGenerated.field.QM31.sub
  V7CompactSemanticFullGenerated.field.QM31.mul
  V7CompactSemanticFullGenerated.field.QM31.square
  V7CompactSemanticFullGenerated.field.QM31.write_le_bytes
  V7CompactSemanticFullGenerated.state_only_hiding.begin_state_only_masked_sumcheck
  V7CompactSemanticFullGenerated.state_only_sumcheck.state_only_boundary_sum
  V7CompactSemanticFullGenerated.state_only_sumcheck.evaluate_state_only_polynomial
  V7CompactSemanticFullGenerated.transcript.Transcript.absorb
  V7CompactSemanticFullGenerated.v6_onefold.V6FixedFieldReader.next_qm31

theorem v7_compact_control_opacity_module_loaded : True := True.intro

#check Aeneas.Std.Result.ok.injEq
#check Aeneas.Std.Result.fail.injEq
#check Aeneas.Std.ControlFlow.cont.injEq
#check Prod.mk.injEq
