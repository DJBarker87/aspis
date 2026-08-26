import AspisFormal.K1.V7Tag73ExactFixedK12PrefixClassifier
import AspisFormal.Pool.V7MerkleFirstUnresolvedBinding

/-!
# Exact fixed Tag-73 K1.2 failure reduction

The executable prefix classifier has four syntactic error constructors.  Two
of them are ordinary verifier obligations: the supplied paths authenticate
and their concrete hash-call traces occur in the final shared oracle log.
Once the Rust/source bridge supplies those facts, this module proves that an
actual K1.2 classifier error is only one of the two random-oracle events that
the counting layer handles:

* a later shared-oracle input hits one of the causally fixed first-unresolved
  path targets; or
* two distinct shared raw inputs have the same 208-bit SHA prefix.

The reduction is deterministic and uses the literal prover-final and
verifier-final histories of the exact fixed scheduler input.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedK12FailureReduction

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerklePartialPathExtractor
open AspisPool.V7MerkleFirstUnresolvedBinding

noncomputable section

theorem exact_prefix_k12_error_under_opening_acceptance_and_coverage
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (openingsAccepted : accepted_two_tree_openings (exactK12Truncate input)
      (exactK12Roots input) (exactK12Openings input))
    (suppliedCovered : ExactPrefixK12SuppliedCoverage input)
    (error : ExactPrefixK12Error input) :
    PrefixPathResolutionFailure (exactK12Truncate input)
        (exactK12ProverPrefixQueries input) (exactK12Roots input)
        (exactK12Openings input) ∨
      RawLogTruncatedDigestCollision (exactK12Truncate input)
        (exactK12OrderedQueries input) := by
  cases error with
  | openingAuthenticationRejected rejected =>
      exact False.elim (rejected openingsAccepted)
  | prefixPathResolution failure =>
      exact Or.inl failure
  | suppliedOpeningTraceMissing missing =>
      exact False.elim (missing suppliedCovered)
  | sharedRawPrefixCollision collision =>
      exact Or.inr collision

theorem exact_prefix_k12_resolution_yields_late_hit_or_collision
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (openingsAccepted : accepted_two_tree_openings (exactK12Truncate input)
      (exactK12Roots input) (exactK12Openings input))
    (suppliedCovered : ExactPrefixK12SuppliedCoverage input)
    (failure : PrefixPathResolutionFailure (exactK12Truncate input)
      (exactK12ProverPrefixQueries input) (exactK12Roots input)
      (exactK12Openings input)) :
    PrefixResolutionLateTargetHit (exactK12Truncate input)
        (exactK12ProverPrefixQueries input) (exactK12OrderedQueries input)
        (exactK12Roots input) (exactK12Openings input) ∨
      RawLogTruncatedDigestCollision (exactK12Truncate input)
        (exactK12OrderedQueries input) := by
  exact accepted_prefixResolutionFailure_yields_late_hit_or_collision
    (exactK12Truncate input) (exactK12ProverPrefixQueries input)
    (exactK12OrderedQueries input) (exactK12Roots input)
    (exactK12Openings input) openingsAccepted
    (exactK12_prover_prefix_is_included_in_full_log input)
    suppliedCovered.1 suppliedCovered.2 failure

/-- The exact deterministic K1.2 endpoint expected from the source bridge.
No classifier constructor remains as an untyped residual event. -/
theorem exact_prefix_k12_error_yields_counted_rom_event
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (openingsAccepted : accepted_two_tree_openings (exactK12Truncate input)
      (exactK12Roots input) (exactK12Openings input))
    (suppliedCovered : ExactPrefixK12SuppliedCoverage input)
    (error : ExactPrefixK12Error input) :
    PrefixResolutionLateTargetHit (exactK12Truncate input)
        (exactK12ProverPrefixQueries input) (exactK12OrderedQueries input)
        (exactK12Roots input) (exactK12Openings input) ∨
      RawLogTruncatedDigestCollision (exactK12Truncate input)
        (exactK12OrderedQueries input) := by
  obtain resolution | collision :=
    exact_prefix_k12_error_under_opening_acceptance_and_coverage
      openingsAccepted suppliedCovered error
  · exact exact_prefix_k12_resolution_yields_late_hit_or_collision
      openingsAccepted suppliedCovered resolution
  · exact Or.inr collision

#print axioms exact_prefix_k12_error_under_opening_acceptance_and_coverage
#print axioms exact_prefix_k12_resolution_yields_late_hit_or_collision
#print axioms exact_prefix_k12_error_yields_counted_rom_event

end

end AspisK1.V7Tag73ExactFixedK12FailureReduction
