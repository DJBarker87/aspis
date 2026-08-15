import Aeneas.Std

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace V5KappaRelationCallerGenerated

/-- The observation adapter stores all four limbs of the scalar passed to the
opaque relation-preparation helper. -/
@[reducible, rust_type "aspis_core::sumcheck::WeightAccumulator"]
def aspis_core.sumcheck.WeightAccumulator :=
  Std.U32 × Std.U32 × Std.U32 × Std.U32

@[reducible, rust_type
  "aspis_verifier_kappa_caller_extraction::v5_cu_probe::private_openings::V5PrivateOpeningRoots"]
def v5_cu_probe.private_openings.V5PrivateOpeningRoots := Unit

@[reducible, rust_type
  "aspis_verifier_kappa_caller_extraction::v5_cu_probe::RelationExtraWork"]
def v5_cu_probe.RelationExtraWork := Unit

@[reducible, rust_type
  "aspis_verifier_kappa_caller_extraction::v5_cu_probe::fri_checks::V5PreparedPcsClaims"]
def v5_cu_probe.fri_checks.V5PreparedPcsClaims := Unit

@[reducible, rust_type
  "aspis_verifier_kappa_caller_extraction::v5_cu_probe::CompactBTerminalWeights"]
def v5_cu_probe.CompactBTerminalWeights := Unit

end V5KappaRelationCallerGenerated
