import AspisFormal.V6AcceptedPathObligations
import AspisFormal.V6PublishedTheoremInterfaces
import AspisFormal.V6SecurityLedger

/-!
# Conditional complete-security endpoint for V6

This is the deliberately conditional capstone requested by the V6
formalisation blueprint.  It does not turn a paper citation, Fiat--Shamir, or
SHA-256 into a Lean theorem.  Instead it packages those boundaries under
typed, named interfaces and proves that their exact V6 event inventory meets
the 100-bit target.

The deterministic accepted path, one-fold algebra, compact-frontier
certificate and query batching are in this import closure.  Explicit-final
hiding and the paired-salt simulator are separate V6 modules because this is
a soundness endpoint, not a theorem that conflates soundness with HVZK.  A
release may cite it only together with concrete inhabitants of the interfaces
below and the separate Rust source bridge.
-/

set_option autoImplicit false

namespace AspisV6ConditionalCompleteSecurity

open AspisSoundnessLedger
open AspisWorkNormalizedEndpoint
open AspisV6PublishedTheoremInterfaces
open AspisV6SecurityLedger

/-- Exact external coding-theorem boundary.  The two predicates are the
profile-specific predicates audited in `V6PublishedTheoremInterfaces`; the
probability consequences include the work factors at their real transcript
positions. -/
structure OneFoldCodeReduction
    {K InitialMessage FinalMessage : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    (initialEncoder : InitialMessage → Fin 1048576 → K)
    (finalEncoder : FinalMessage → Fin 262144 → K) where
  initialPublished : PublishedInitialWidth29CurveDecodability initialEncoder
  foldPublished : PublishedOneFoldCurveDecodability finalEncoder
  initialBatchFailure : Real
  oneFoldFailure : Real
  initialBatchFailureNonnegative : 0 ≤ initialBatchFailure
  oneFoldFailureNonnegative : 0 ≤ oneFoldFailure
  initialBatchBound : initialBatchFailure ≤ (1 : Real) / 2 ^ 109
  oneFoldBound : oneFoldFailure ≤ (1 : Real) / 2 ^ 111

/-- Every non-coding interactive event in the V6 ledger, named once.  The
`eventUnion` field is the failure-event-inclusion boundary: a false accepted
interactive transcript must enter this one explicit union. -/
structure InteractiveFailureReduction
    {K InitialMessage FinalMessage : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    {initialEncoder : InitialMessage → Fin 1048576 → K}
    {finalEncoder : FinalMessage → Fin 262144 → K}
    (coding : OneFoldCodeReduction initialEncoder finalEncoder) where
  compactQueryFailure : Real
  queryBatchCollision : Real
  oodFailure : Real
  relationRoundFailure : Real
  thetaCollision : Real
  threePointBatchCollision : Real
  inactiveCopyCollision : Real
  tupleCompressionCollision : Real
  copyRangePoleCollision : Real
  zerocheckEqualityCollision : Real
  zeroSumHelperCollision : Real
  etaZero : Real
  semanticSumcheckRoundCollision : Real
  primitiveReserve : Real
  compilerReserve : Real
  roundFailure : Real
  roundFailureNonnegative : 0 ≤ roundFailure
  eventUnion :
    roundFailure ≤
      coding.initialBatchFailure + coding.oneFoldFailure +
      compactQueryFailure + queryBatchCollision + oodFailure +
      relationRoundFailure + thetaCollision + threePointBatchCollision +
      inactiveCopyCollision + tupleCompressionCollision +
      copyRangePoleCollision + zerocheckEqualityCollision +
      zeroSumHelperCollision + etaZero + semanticSumcheckRoundCollision +
      primitiveReserve + compilerReserve
  compactQueryBound : compactQueryFailure ≤ (1 : Real) / 2 ^ 109
  queryBatchBound : queryBatchCollision ≤ (1 : Real) / 2 ^ 120
  oodBound : oodFailure ≤ (1 : Real) / 2 ^ 213
  relationRoundBound : relationRoundFailure ≤ (1 : Real) / 2 ^ 119
  thetaBound : thetaCollision ≤ (1 : Real) / 2 ^ 119
  threePointBound : threePointBatchCollision ≤ (1 : Real) / 2 ^ 119
  inactiveCopyBound : inactiveCopyCollision ≤ (1 : Real) / 2 ^ 119
  tupleCompressionBound : tupleCompressionCollision ≤ (1 : Real) / 2 ^ 112
  copyRangePoleBound : copyRangePoleCollision ≤ (1 : Real) / 2 ^ 111
  zerocheckEqualityBound : zerocheckEqualityCollision ≤ (1 : Real) / 2 ^ 120
  zeroSumHelperBound : zeroSumHelperCollision ≤ (1 : Real) / 2 ^ 123
  etaZeroBound : etaZero ≤ (1 : Real) / 2 ^ 123
  semanticSumcheckRoundBound :
    semanticSumcheckRoundCollision ≤ (1 : Real) / 2 ^ 115
  primitiveReserveBound : primitiveReserve ≤ (1 : Real) / 2 ^ 124
  compilerReserveBound : compilerReserve ≤ (1 : Real) / 2 ^ 128

/-- Classical Fiat--Shamir/work-normalisation boundary.  The selector union is
already the factor three in `compiledBound`; it must not be applied again. -/
structure ClassicalFSCompiler (roundFailure : Real) where
  adversaryWork : Real
  publicCoinRounds : Real
  capacityError : Real
  coreAdvantage : Real
  workAtLeastOne : 1 ≤ adversaryWork
  workAtMost : adversaryWork ≤ 2 ^ 128
  roundsNonnegative : 0 ≤ publicCoinRounds
  roundsAtMost : publicCoinRounds ≤ 30
  capacityNonnegative : 0 ≤ capacityError
  capacityBound : capacityError ≤ (1 : Real) / 2 ^ 256
  compiledBound :
    coreAdvantage ≤
      3 * bcsError roundFailure adversaryWork publicCoinRounds capacityError

/-- External implementation/primitive allowance.  The internal event ledger
does not silently consume this term.  Its supporting release table must name
SHA-256 implementation faithfulness, collision/preimage/ROM assumptions,
Poseidon2 faithfulness, Merkle binding, and source correspondence separately. -/
structure HashAndImplementationInterfaces where
  externalAdvantage : Real
  externalNonnegative : 0 ≤ externalAdvantage
  externalBound : externalAdvantage ≤ (1 : Real) / (2 * 2 ^ 100)

/-- The named interactive inventory is no larger than the exact rounded V6
round bound used by the BCS theorem. -/
theorem round_failure_le_conditional_upper
    {K InitialMessage FinalMessage : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    {initialEncoder : InitialMessage → Fin 1048576 → K}
    {finalEncoder : FinalMessage → Fin 262144 → K}
    (coding : OneFoldCodeReduction initialEncoder finalEncoder)
    (events : InteractiveFailureReduction coding) :
    events.roundFailure ≤ conditionalRoundUpper := by
  unfold conditionalRoundUpper queryBatchCollisionUpper
    inheritedZerocheckEqualityUpper
  linarith [coding.initialBatchBound, coding.oneFoldBound,
    events.eventUnion, events.compactQueryBound, events.queryBatchBound,
    events.oodBound, events.relationRoundBound, events.thetaBound,
    events.threePointBound, events.inactiveCopyBound,
    events.tupleCompressionBound, events.copyRangePoleBound,
    events.zerocheckEqualityBound, events.zeroSumHelperBound,
    events.etaZeroBound, events.semanticSumcheckRoundBound,
    events.primitiveReserveBound, events.compilerReserveBound]

/-- Conditional 100-bit V6 endpoint.  All finite arithmetic is discharged in
Lean; the remaining premises are exactly the named coding, event-inclusion,
Fiat--Shamir and primitive/source interfaces above. -/
theorem v6_onefold_soundness_conditional
    {K InitialMessage FinalMessage : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    {initialEncoder : InitialMessage → Fin 1048576 → K}
    {finalEncoder : FinalMessage → Fin 262144 → K}
    (coding : OneFoldCodeReduction initialEncoder finalEncoder)
    (events : InteractiveFailureReduction coding)
    (fs : ClassicalFSCompiler events.roundFailure)
    (hashAndImplementation : HashAndImplementationInterfaces) :
    fs.coreAdvantage + hashAndImplementation.externalAdvantage ≤
      (1 : Real) / 2 ^ 100 := by
  have hbcs := conditional_work_normalized_core_le_one_half
    events.roundFailure fs.publicCoinRounds fs.capacityError fs.adversaryWork
    events.roundFailureNonnegative
    (round_failure_le_conditional_upper coding events)
    fs.roundsNonnegative fs.roundsAtMost
    fs.capacityNonnegative fs.capacityBound
    fs.workAtLeastOne fs.workAtMost
  have hcore : fs.coreAdvantage ≤ (1 : Real) / (2 * 2 ^ 100) :=
    fs.compiledBound.trans hbcs
  exact conditional_core_plus_external_meets_100_bits
    fs.coreAdvantage hashAndImplementation.externalAdvantage
    hcore hashAndImplementation.externalBound

#print axioms round_failure_le_conditional_upper
#print axioms v6_onefold_soundness_conditional

end AspisV6ConditionalCompleteSecurity
