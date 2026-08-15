import Aeneas.Std

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace V5KappaCompositeCallerGenerated

@[reducible, rust_type "aspis_core::transcript::Transcript"]
def aspis_core.transcript.Transcript := Unit

@[reducible, rust_type
  "aspis_statement::atomic_statement::AtomicPaymentStatementV4"]
def aspis_statement.atomic_statement.AtomicPaymentStatementV4 := Unit

@[reducible, rust_type
  "aspis_verifier_kappa_caller_extraction::v5_cu_probe::private_openings::V5PrivateOpeningRoots"]
def v5_cu_probe.private_openings.V5PrivateOpeningRoots := Unit

@[reducible, rust_type
  "aspis_verifier_kappa_caller_extraction::v5_cu_probe::fri_checks::V5PreparedPcsClaims"]
def v5_cu_probe.fri_checks.V5PreparedPcsClaims := Unit

end V5KappaCompositeCallerGenerated
