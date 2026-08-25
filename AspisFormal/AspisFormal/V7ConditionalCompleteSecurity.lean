import AspisFormal.V6AcceptedPathObligations
import AspisFormal.V6HidingFinalFactorization
import AspisFormal.V6PairedSaltHiding
import AspisFormal.V7AuthenticatedWire
import AspisFormal.V7CompactSecurityLedger

/-!
# Conditional soundness endpoint for V7

V7 preserves V6's width-29 arithmetic, semantic terminal, one fold, complete
final vector and paired 256-bit salts.  It changes the authenticated wire to
complete C2 fibres, one cap-203 counter stream and 208-bit Merkle digests.

This capstone keeps the published coding theorem, Fiat--Shamir compiler,
SHA-256/Merkle, and source-correspondence boundaries explicit.  Lean proves
the exact false-acceptance event arithmetic and the final 100-bit soundness
composition; it does not turn any external primitive or paper statement into
an axiom.

The imported accepted-path, final-factorization, paired-salt, and complete-C2
modules remain separate results.  The theorem below does **not** conclude
HVZK, deployed source correspondence, state-transition security, or theft
resistance, and those properties must not be inferred merely from this import
closure.
-/

set_option autoImplicit false

namespace AspisV7ConditionalCompleteSecurity

open AspisSoundnessLedger
open AspisWorkNormalizedEndpoint
open AspisV6PublishedTheoremInterfaces
open AspisV7CompactSecurityLedger

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
  initialBatchBound : initialBatchFailure ≤ exactInitialBatchUpper
  oneFoldBound : oneFoldFailure ≤ exactOneFoldUpper

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
  compactQueryBound : compactQueryFailure ≤ exactCompactQueryUpper
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

/-- V7 has one enforced first-success counter stream, so no outer selector
union factor appears in this compiler boundary. -/
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
      bcsError roundFailure adversaryWork publicCoinRounds capacityError

/-- The 208-bit digest contributes at most the generic 104-bit classical
collision term.  `otherExternalAdvantage` is an explicit aggregate boundary
for every other primitive/source event; a release must split and justify that
aggregate in its external-assumption ledger. -/
structure HashAndImplementationInterfaces where
  digestCollisionAdvantage : Real
  otherExternalAdvantage : Real
  externalAdvantage : Real
  digestNonnegative : 0 ≤ digestCollisionAdvantage
  otherNonnegative : 0 ≤ otherExternalAdvantage
  externalComposition :
    externalAdvantage ≤ digestCollisionAdvantage + otherExternalAdvantage
  digestCollisionBound :
    digestCollisionAdvantage ≤ (1 : Real) / 2 ^ 104
  otherExternalBound :
    otherExternalAdvantage ≤ (7 : Real) / (16 * 2 ^ 100)

theorem round_failure_le_conditional_upper
    {K InitialMessage FinalMessage : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    {initialEncoder : InitialMessage → Fin 1048576 → K}
    {finalEncoder : FinalMessage → Fin 262144 → K}
    (coding : OneFoldCodeReduction initialEncoder finalEncoder)
    (events : InteractiveFailureReduction coding) :
    events.roundFailure ≤ conditionalRoundUpperExact := by
  unfold conditionalRoundUpperExact
  linarith [coding.initialBatchBound, coding.oneFoldBound,
    events.eventUnion, events.compactQueryBound, events.queryBatchBound,
    events.oodBound, events.relationRoundBound, events.thetaBound,
    events.threePointBound, events.inactiveCopyBound,
    events.tupleCompressionBound, events.copyRangePoleBound,
    events.zerocheckEqualityBound, events.zeroSumHelperBound,
    events.etaZeroBound, events.semanticSumcheckRoundBound,
    events.primitiveReserveBound, events.compilerReserveBound]

theorem external_advantage_le_one_half
    (interfaces : HashAndImplementationInterfaces) :
    interfaces.externalAdvantage ≤ (1 : Real) / (2 * 2 ^ 100) := by
  calc
    interfaces.externalAdvantage ≤
        interfaces.digestCollisionAdvantage +
          interfaces.otherExternalAdvantage := interfaces.externalComposition
    _ ≤ (1 : Real) / 2 ^ 104 + (7 : Real) / (16 * 2 ^ 100) := by
      gcongr
      · exact interfaces.digestCollisionBound
      · exact interfaces.otherExternalBound
    _ = (1 : Real) / (2 * 2 ^ 100) := by norm_num

/-- Conditional 100-bit false-acceptance bound for the V7 one-fold profile.
Its premises are the named coding, event-inclusion, Fiat--Shamir/work, and
primitive/source interfaces above.  This is a soundness theorem, not an
unconditional deployed theft-resistance theorem. -/
theorem v7_onefold_soundness_conditional
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
  calc
    fs.coreAdvantage + hashAndImplementation.externalAdvantage ≤
        (1 : Real) / (2 * 2 ^ 100) + (1 : Real) / (2 * 2 ^ 100) :=
      add_le_add hcore (external_advantage_le_one_half hashAndImplementation)
    _ = (1 : Real) / 2 ^ 100 := by norm_num

#print axioms round_failure_le_conditional_upper
#print axioms external_advantage_le_one_half
#print axioms v7_onefold_soundness_conditional

end AspisV7ConditionalCompleteSecurity
