import AspisFormal.V5TranscriptSourceAdapter

/-!
# Normalized successful path of the extracted V5 prefix helper

This file is the small typed form checked against the pinned Aeneas output by
`aeneas-verif/v5-transcript-prefix-20260815/check-normalized-success-path.py`.
It records the transcript-affecting external calls, their arguments, the
values returned by those calls, the terminal-context comparison, and the
successful return value.

The checked normalization deliberately removes parser and rejection branches
and retains only the branch ending in `Result.Ok`.  It is not a second source
extraction and it is not claimed to be definitionally equal to the generated
function, whose external transcript operations are opaque.
-/

namespace AspisV5TranscriptPrefixNormalizedGenerated

open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5NonceWorkAuthentication
open AspisV5TranscriptConnection

/-- Values decoded from the accepted wire or returned by the semantic
sumcheck, beyond the values already named in `V5DerivedValues`. -/
structure PrefixSuccessfulValues (FieldValue : Type*) where
  initialClaim : FieldValue
  terminalClaim : FieldValue
  terminalReal : FieldValue
  terminalMask : FieldValue
  terminalMasked : FieldValue
  inactiveClaim : FieldValue

/-- The external calls retained from the successful generated branch.
Challenge results and compound-helper results are fields of the constructors,
so later dataflow is not represented only by names in prose. -/
inductive PrefixExternalCall (FieldValue : Type*) where
  | absorb (slot : AbsorbSlot) (label : Byte) (payload : List Byte)
  | absorbRoundRoot
      (round : Fin 4) (root : List Byte) (publicSalt : List Byte)
  | challengeQm31 (slot : SqueezeSlot) (result : FieldValue)
  | absorbC2Root (root : List Byte) (publicSalt : List Byte)
  | beginZerocheck
      (theta : FieldValue) (point : Fin 10 → FieldValue) (mu : FieldValue)
  | beginMaskedSumcheck (initialClaim eta : FieldValue)
  | verifySemanticSumcheck
      (wire : List Byte) (initialClaim : FieldValue)
      (roundChallenges : Fin 10 → FieldValue) (terminalClaim : FieldValue)
  | checkAndAbsorbBatchNonce (nonce : Nonce64)
  | challengeNonzeroQm31 (slot : SqueezeSlot) (result : FieldValue)

/-- The single slice passed to `verify_state_only_sumcheck_streaming`, written
as the ten consecutive 448-byte rounds projected by the maintained input. -/
def semanticSumcheckWire (input : V5TranscriptInputs) : List Byte :=
  (List.ofFn (fun round : Fin 10 => bytes (input.semanticSumcheck round))).flatten

/-- Typed normalization of all transcript-affecting external calls on the
successful branch of the pinned generated function. -/
def generatedSuccessfulPrefixCalls
    {FieldValue PointValue : Type*}
    (input : V5TranscriptInputs)
    (derived : V5DerivedValues FieldValue PointValue)
    (values : PrefixSuccessfulValues FieldValue) :
    List (PrefixExternalCall FieldValue) :=
  [.absorb .profile (AbsorbSlot.label .profile) profileDomain,
    .absorb .basis (AbsorbSlot.label .basis) circleBasisIdentifier,
    .absorb .statement (AbsorbSlot.label .statement)
      (bytes input.statementDigest),
    .absorbRoundRoot 0 (bytes (input.circleRoot 0))
      (bytes (input.publicSalt 0)),
    .challengeQm31 .lambda derived.lambda,
    .challengeQm31 .chi derived.chi,
    .absorbC2Root (bytes input.c2Root) (bytes (input.publicSalt 1)),
    .beginZerocheck derived.theta derived.zerocheckPoint derived.mu,
    .beginMaskedSumcheck values.initialClaim derived.eta,
    .verifySemanticSumcheck (semanticSumcheckWire input) values.initialClaim
      derived.relationChallenge values.terminalClaim,
    .absorb .relationPoints (AbsorbSlot.label .relationPoints)
      (bytes input.relationPoints),
    .absorb .statementEvaluations (AbsorbSlot.label .statementEvaluations)
      (bytes input.statementEvaluations),
    .absorb .terminalClaims (AbsorbSlot.label .terminalClaims)
      (bytes input.terminalClaims),
    .checkAndAbsorbBatchNonce input.batchNonce,
    .challengeNonzeroQm31 .gamma derived.gamma,
    .absorb .inactiveClaim (AbsorbSlot.label .inactiveClaim)
      (bytes input.inactiveClaim),
    .challengeNonzeroQm31 .kappa derived.kappa]

/-- The value compared with the decoded terminal context. -/
structure GeneratedTerminalContext (FieldValue : Type*) where
  lambda : FieldValue
  chi : FieldValue
  theta : FieldValue
  zerocheckPoint : Fin 10 → FieldValue
  mu : FieldValue
  eta : FieldValue

def generatedTerminalContext
    {FieldValue PointValue : Type*}
    (derived : V5DerivedValues FieldValue PointValue) :
    GeneratedTerminalContext FieldValue where
  lambda := derived.lambda
  chi := derived.chi
  theta := derived.theta
  zerocheckPoint := derived.zerocheckPoint
  mu := derived.mu
  eta := derived.eta

/-- Fields returned in `VerifiedRealV5Wire` on the successful branch. -/
structure GeneratedPrefixReturn (FieldValue : Type*) where
  eta : FieldValue
  roundChallenges : Fin 10 → FieldValue
  gamma : FieldValue
  kappa : FieldValue
  terminalReal : FieldValue
  terminalMask : FieldValue
  terminalMasked : FieldValue
  inactiveClaim : FieldValue

def generatedPrefixReturn
    {FieldValue PointValue : Type*}
    (derived : V5DerivedValues FieldValue PointValue)
    (values : PrefixSuccessfulValues FieldValue) :
    GeneratedPrefixReturn FieldValue where
  eta := derived.eta
  roundChallenges := derived.relationChallenge
  gamma := derived.gamma
  kappa := derived.kappa
  terminalReal := values.terminalReal
  terminalMask := values.terminalMask
  terminalMasked := values.terminalMasked
  inactiveClaim := values.inactiveClaim

end AspisV5TranscriptPrefixNormalizedGenerated
