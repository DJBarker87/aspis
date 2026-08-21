import V5FriCallerMerkleBridge
import V5FriConsumerObservationBridge
import AspisFormal.V5AcceptedExecutionReleasedSecurity

/-!
# Accepted production caller to released observation

This file joins the extracted outer caller, the independently translated
Merkle verifier, and the concrete accepted FRI-call resolver.  Its main result
derives the maintained parser/output equality instead of taking that equality
as an independent premise.

Three source/tool statements are explicit inputs.  First,
`AcceptedCallerMerkleSourceEquality` is the exact one-call wrapper which fixes
the production SHA-256 callback.  Second,
the fixed-inverse FRI wrapper must retain the opening returned by the Merkle
call.  Third, `AcceptedVerifierExecutionBuildsProductionCallerEnvironment`
states that an accepted outer verifier execution supplies the parsed input,
queries, challenges, successful caller result, and input bindings recorded by
the concrete environment.  The theorem below derives the former observation
and whole-consumer equalities; neither is accepted as a free input.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriCallerAcceptedResolverBridge

open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleConsumedValueBridge
open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedExecutionReleasedSchedule
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriCompatibleCandidateChain
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriGlobalCausalStrategy
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriRelationCandidateBridge
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5MerkleRustBridge
open AspisV5NonceWorkAuthentication
open AspisV5RelationStressSourceBridge
open AspisV5Tag67AcceptedFalseInclusion
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67ModeledRelationAcceptanceBridge
open AspisV5Tag67RelationListInclusion
open AspisV5TranscriptConnection
open AspisV5WithoutReplacementQuerySoundness

/-- The five generated root-array entries determine one maintained root tuple.
This is a structural fact, not a hash assumption. -/
theorem generatedRootsMatch_unique
    {rootsArray : Array
      AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedDigest 5#usize}
    {left right : V5PrivateRoots AspisV5MerkleRustBridge.Digest32}
    (hleft : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedRootsMatch
      rootsArray left)
    (hright : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedRootsMatch
      rootsArray right) :
    left = right := by
  rcases hleft with
    ⟨lc1, lc2, lline1, lline2, lline3, hlc1, hlc2, hlline1,
      hlline2, hlline3, leftC1, leftC2, leftLine1, leftLine2, leftLine3⟩
  rcases hright with
    ⟨rc1, rc2, rline1, rline2, rline3, hrc1, hrc2, hrline1,
      hrline2, hrline3, rightC1, rightC2, rightLine1, rightLine2,
      rightLine3⟩
  have c1Eq : lc1 = rc1 := Result.ok.inj (hlc1.symm.trans hrc1)
  have c2Eq : lc2 = rc2 := Result.ok.inj (hlc2.symm.trans hrc2)
  have line1Eq : lline1 = rline1 :=
    Result.ok.inj (hlline1.symm.trans hrline1)
  have line2Eq : lline2 = rline2 :=
    Result.ok.inj (hlline2.symm.trans hrline2)
  have line3Eq : lline3 = rline3 :=
    Result.ok.inj (hlline3.symm.trans hrline3)
  cases left
  cases right
  simp_all

/-- Evidence for one successful high-level resolver result.  Every field is
observable at the translated caller boundary.  In particular, the opening
returned by the Merkle call is the same structural value stored in the
accepted FRI call; it cannot be replaced by a separately parsed value. -/
structure AcceptedResolverCallerWitness
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (call : AspisV5MerkleRustBridge.V5ProductionCall)
    (acceptedCall : AspisV5FriConsumerObservationBridge.AcceptedFriCall) :
    Type where
  parsed : AspisV5FriCallerParametric.Parsed
  queries : Array Std.U32 18#usize
  finalPolynomial : Array AspisV5FriCallerParametric.QM31 4#usize
  alphas : Array AspisV5FriCallerParametric.QM31 4#usize
  gamma : AspisV5FriCallerParametric.QM31
  output : AspisV5FriCallerParametric.QM31 ×
    AspisV5FriCallerParametric.Prepared
  prepareCall : AspisV5FriCallerParametric.PrepareCall
  friCall : AspisV5FriCallerParametric.FriCall
  trace : AspisV5FriCallerParametric.AcceptedCallerTrace openingsCall
    prepareCall friCall parsed queries finalPolynomial alphas gamma output
  acceptedOpening_eq : acceptedCall.openings =
    AspisV5MerkleFriReturnedOutputBridge.toFriVerified
      (AspisV5FriCallerMerkleBridge.toMerkleVerified trace.opening)
  queryCount : call.queries.card = 18
  queryModel :
    (V5MerkleQueryReuseProof.expectedLayer0
        (Array.to_slice queries).val).map (fun index => index.val) =
      AspisV5TopologyConstruction.sharedLevelIndices call.queries 0
  rootsArray : Array
    AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedDigest 5#usize
  parsedRoots_eq :
    (AspisV5FriCallerMerkleBridge.toMerkleRoots
      parsed.v5_private_roots).as_array =
      .ok rootsArray
  rootsMatch :
    AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedRootsMatch
      rootsArray call.roots
  proofBytes_eq :
    parsed.v5_private_proof.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte =
      call.proofBytes

/-- Universal connection between the concrete accepted-call resolver and the
translated production caller.  This records input binding and the identity of
the returned opening; it does not assume any Merkle or FRI mathematics. -/
def AcceptedResolverUsesProductionCaller
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (resolve : AspisV5MerkleRustBridge.V5ProductionCall →
      Option AspisV5FriConsumerObservationBridge.AcceptedFriCall) : Prop :=
  ∀ call acceptedCall, resolve call = some acceptedCall →
    Nonempty (AcceptedResolverCallerWitness openingsCall hash call
      acceptedCall)

/-- The translated caller plus the exact one-call Merkle wrapper supplies the
parser/output premise used by the maintained released-security theorem. -/
theorem accepted_resolver_caller_implies_parser_output_equality
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (resolve : AspisV5MerkleRustBridge.V5ProductionCall →
      Option AspisV5FriConsumerObservationBridge.AcceptedFriCall)
    (hsource :
      AspisV5FriCallerMerkleBridge.AcceptedCallerMerkleSourceEquality
        openingsCall hash)
    (hhash : AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
      sha256 hash)
    (hcaller : AcceptedResolverUsesProductionCaller openingsCall hash
      resolve) :
    ExactRustV5OpeningParserOutputEquality sha256
      (AspisV5FriConsumerObservationBridge.observationFromAcceptedResolver
        resolve) := by
  intro call observation hobservation
  unfold AspisV5FriConsumerObservationBridge.observationFromAcceptedResolver
    at hobservation
  cases hresolved : resolve call with
  | none => simp [hresolved] at hobservation
  | some acceptedCall =>
      simp only [hresolved, Option.map_some, Option.some.injEq] at hobservation
      subst observation
      obtain ⟨witness⟩ := hcaller call acceptedCall hresolved
      obtain ⟨rootsArray, modelRoots, run, rootsArrayEq, rootsMatch,
          proofBytesEq, driverEq⟩ :=
        AspisV5FriCallerMerkleBridge.accepted_caller_opening_yields_exact_merkle_and_fri_view
          sha256 call.queries witness.queryCount hash openingsCall
          witness.prepareCall witness.friCall witness.parsed witness.queries
          witness.finalPolynomial witness.alphas witness.gamma witness.output
          witness.trace hsource hhash witness.queryModel
      have rootsArrayUnique : rootsArray = witness.rootsArray :=
        Result.ok.inj (rootsArrayEq.symm.trans witness.parsedRoots_eq)
      have modelRootsEq : modelRoots = call.roots :=
        generatedRootsMatch_unique
          (rootsArrayUnique ▸ rootsMatch) witness.rootsMatch
      subst modelRoots
      refine ⟨run, proofBytesEq.trans witness.proofBytes_eq, ?_⟩
      calc
        (AspisV5FriConsumerObservationBridge.AcceptedFriCall.observation
            acceptedCall).driver =
            AspisV5FriConsumerObservationBridge.generatedDriverOutput
              acceptedCall.openings := rfl
        _ = AspisV5FriConsumerObservationBridge.generatedDriverOutput
              (AspisV5MerkleFriReturnedOutputBridge.toFriVerified
                (AspisV5FriCallerMerkleBridge.toMerkleVerified
                  witness.trace.opening)) := by
              rw [witness.acceptedOpening_eq]
        _ = driverOutputOfRun run [] := driverEq

/-- The concrete FRI observation adapter already proves the four source read
loops.  Combining that theorem with the parser result removes the former
whole-consumer equality premise. -/
theorem accepted_resolver_caller_implies_consumer_equality
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (resolve : AspisV5MerkleRustBridge.V5ProductionCall →
      Option AspisV5FriConsumerObservationBridge.AcceptedFriCall)
    (hsource :
      AspisV5FriCallerMerkleBridge.AcceptedCallerMerkleSourceEquality
        openingsCall hash)
    (hhash : AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
      sha256 hash)
    (hcaller : AcceptedResolverUsesProductionCaller openingsCall hash
      resolve) :
    ExactRustV5OpeningAndFriConsumerEquality sha256
      (AspisV5FriConsumerObservationBridge.observationFromAcceptedResolver
        resolve) := by
  apply
    AspisV5FriConsumerObservationBridge.opening_parser_and_accepted_resolver_imply_consumer_equality
  exact accepted_resolver_caller_implies_parser_output_equality sha256 hash
    openingsCall resolve hsource hhash hcaller

/-- Inputs and one successful result of the translated outer caller.  This is
the information absent from the deliberately small `V5ProductionCall`, which
contains only roots, query set, and proof bytes.

The `acceptedOpening_of_fri_success` field is the focused source edge for the
second one-call wrapper: a successful FRI call stores the same opening value
in the concrete accepted-call record.  It does not assert any FRI arithmetic
property; `AcceptedFriCall.accepted` carries the actual extracted acceptance. -/
structure ProductionCallerEnvironment
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (call : AspisV5MerkleRustBridge.V5ProductionCall) : Type where
  acceptedCall : AspisV5FriConsumerObservationBridge.AcceptedFriCall
  parsed : AspisV5FriCallerParametric.Parsed
  queries : Array Std.U32 18#usize
  finalPolynomial : Array AspisV5FriCallerParametric.QM31 4#usize
  alphas : Array AspisV5FriCallerParametric.QM31 4#usize
  gamma : AspisV5FriCallerParametric.QM31
  output : AspisV5FriCallerParametric.QM31 ×
    AspisV5FriCallerParametric.Prepared
  prepareCall : AspisV5FriCallerParametric.PrepareCall
  friCall : AspisV5FriCallerParametric.FriCall
  caller_run : AspisV5FriCallerParametric.verifyFriPhaseWith openingsCall
    prepareCall friCall parsed queries finalPolynomial alphas gamma =
      .ok (.Ok output)
  acceptedOpening_of_fri_success :
    ∀ opening prepared sink,
      friCall opening prepared alphas finalPolynomial = .ok (.Ok sink) →
        acceptedCall.openings =
          AspisV5MerkleFriReturnedOutputBridge.toFriVerified
            (AspisV5FriCallerMerkleBridge.toMerkleVerified opening)
  queryCount : call.queries.card = 18
  queryModel :
    (V5MerkleQueryReuseProof.expectedLayer0
        (Array.to_slice queries).val).map (fun index => index.val) =
      AspisV5TopologyConstruction.sharedLevelIndices call.queries 0
  rootsArray : Array
    AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedDigest 5#usize
  parsedRoots_eq :
    (AspisV5FriCallerMerkleBridge.toMerkleRoots
      parsed.v5_private_roots).as_array = .ok rootsArray
  rootsMatch :
    AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedRootsMatch
      rootsArray call.roots
  proofBytes_eq :
    parsed.v5_private_proof.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte =
      call.proofBytes

/-- The one remaining outer-entry source statement.  It says exactly that a
successful execution of the deployed verifier supplies the concrete values
and successful FRI call recorded by `ProductionCallerEnvironment`.

The existing extracted composite caller proves the call order from prefix
verification through the FRI and relation phases.  The transcript bundle
proves the values returned by the prefix/replay/query path.  Neither artifact
translates the `AccountInfo` borrow-and-parse entry point or the two
higher-ranked callback wrappers, so this implication is kept as one named
source edge instead of being hidden inside an observation function. -/
def AcceptedVerifierExecutionBuildsProductionCallerEnvironment
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (verifierAccepts : AspisV5MerkleRustBridge.V5ProductionCall → Prop) :
    Prop :=
  ∀ call, verifierAccepts call →
    Nonempty (ProductionCallerEnvironment openingsCall hash call)

/-- A dependent single-call environment.  This lets one concrete accepted
verifier execution feed the universal observation API without assuming
anything about calls which were not executed. -/
noncomputable def singleProductionCallerEnvironment
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (target : AspisV5MerkleRustBridge.V5ProductionCall)
    (targetEnvironment : ProductionCallerEnvironment openingsCall hash
      target) :
    (call : AspisV5MerkleRustBridge.V5ProductionCall) →
      Option (ProductionCallerEnvironment openingsCall hash call) :=
  fun call => by
    classical
    exact if h : call = target then
      some (h.symm ▸ targetEnvironment)
    else none

@[simp] theorem singleProductionCallerEnvironment_at_target
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (target : AspisV5MerkleRustBridge.V5ProductionCall)
    (targetEnvironment : ProductionCallerEnvironment openingsCall hash
      target) :
    singleProductionCallerEnvironment openingsCall hash target
      targetEnvironment target = some targetEnvironment := by
  classical
  simp [singleProductionCallerEnvironment]

/-- Concrete high-level resolver obtained by running the translated caller in
the supplied production environment and retaining its accepted FRI call. -/
def resolveFromProductionCaller
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (environment : (call : AspisV5MerkleRustBridge.V5ProductionCall) →
      Option (ProductionCallerEnvironment openingsCall hash call)) :
    AspisV5MerkleRustBridge.V5ProductionCall →
      Option AspisV5FriConsumerObservationBridge.AcceptedFriCall :=
  fun call => (environment call).map
    ProductionCallerEnvironment.acceptedCall

/-- The concrete resolver satisfies the former universal caller-connection
premise.  The accepted caller trace is obtained from the translated caller
result; it is not supplied in the environment. -/
theorem resolveFromProductionCaller_uses_production_caller
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (environment : (call : AspisV5MerkleRustBridge.V5ProductionCall) →
      Option (ProductionCallerEnvironment openingsCall hash call)) :
    AcceptedResolverUsesProductionCaller openingsCall hash
      (resolveFromProductionCaller openingsCall hash environment) := by
  intro call acceptedCall hresolve
  unfold resolveFromProductionCaller at hresolve
  cases henv : environment call with
  | none => simp [henv] at hresolve
  | some env =>
      simp only [henv, Option.map_some, Option.some.injEq] at hresolve
      subst acceptedCall
      obtain ⟨trace⟩ :=
        AspisV5FriCallerParametric.accepted_fri_phase_yields_exact_call_trace
          openingsCall env.prepareCall env.friCall env.parsed env.queries
          env.finalPolynomial env.alphas env.gamma env.output env.caller_run
      exact ⟨{
        parsed := env.parsed
        queries := env.queries
        finalPolynomial := env.finalPolynomial
        alphas := env.alphas
        gamma := env.gamma
        output := env.output
        prepareCall := env.prepareCall
        friCall := env.friCall
        trace := trace
        acceptedOpening_eq :=
          env.acceptedOpening_of_fri_success trace.opening trace.prepared
            trace.sink trace.fri_run
        queryCount := env.queryCount
        queryModel := env.queryModel
        rootsArray := env.rootsArray
        parsedRoots_eq := env.parsedRoots_eq
        rootsMatch := env.rootsMatch
        proofBytes_eq := env.proofBytes_eq
      }⟩

/-- Consumer equality for the concrete resolver, with no free universal
`AcceptedResolverUsesProductionCaller` premise. -/
theorem production_caller_environment_implies_consumer_equality
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (environment : (call : AspisV5MerkleRustBridge.V5ProductionCall) →
      Option (ProductionCallerEnvironment openingsCall hash call))
    (hsource :
      AspisV5FriCallerMerkleBridge.AcceptedCallerMerkleSourceEquality
        openingsCall hash)
    (hhash : AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
      sha256 hash) :
    ExactRustV5OpeningAndFriConsumerEquality sha256
      (AspisV5FriConsumerObservationBridge.observationFromAcceptedResolver
        (resolveFromProductionCaller openingsCall hash environment)) := by
  apply accepted_resolver_caller_implies_consumer_equality sha256 hash
    openingsCall (resolveFromProductionCaller openingsCall hash environment)
    hsource hhash
  exact resolveFromProductionCaller_uses_production_caller openingsCall hash
    environment

/-- Specialization to the explicit one-call Merkle wrapper.  Its successful
result equality is a theorem, so callers need supply only the production
SHA-256 callback equality. -/
theorem exact_production_caller_environment_implies_consumer_equality
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (environment : (call : AspisV5MerkleRustBridge.V5ProductionCall) →
      Option (ProductionCallerEnvironment
        (AspisV5FriCallerMerkleBridge.exactMerkleOpeningCall hash) hash call))
    (hhash : AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
      sha256 hash) :
    ExactRustV5OpeningAndFriConsumerEquality sha256
      (AspisV5FriConsumerObservationBridge.observationFromAcceptedResolver
        (resolveFromProductionCaller
          (AspisV5FriCallerMerkleBridge.exactMerkleOpeningCall hash) hash
          environment)) := by
  exact production_caller_environment_implies_consumer_equality sha256 hash
    (AspisV5FriCallerMerkleBridge.exactMerkleOpeningCall hash) environment
    (AspisV5FriCallerMerkleBridge.exactMerkleOpeningCall_sourceEquality hash)
    hhash

/-- One accepted outer-verifier execution now constructs both the concrete
observation and the exact Merkle/FRI consumer theorem needed downstream.  No
free observation equality or total resolver is supplied by the caller of this
theorem: the resolver is the dependent single-call environment above. -/
theorem accepted_verifier_execution_builds_production_caller_observation
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (verifierAccepts : AspisV5MerkleRustBridge.V5ProductionCall → Prop)
    (hentry : AcceptedVerifierExecutionBuildsProductionCallerEnvironment
      openingsCall hash verifierAccepts)
    (hsource :
      AspisV5FriCallerMerkleBridge.AcceptedCallerMerkleSourceEquality
        openingsCall hash)
    (hhash : AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
      sha256 hash)
    (target : AspisV5MerkleRustBridge.V5ProductionCall)
    (haccepted : verifierAccepts target) :
    ∃ targetEnvironment : ProductionCallerEnvironment openingsCall hash target,
      let environment := singleProductionCallerEnvironment openingsCall hash
        target targetEnvironment
      let rustObservation :=
        AspisV5FriConsumerObservationBridge.observationFromAcceptedResolver
          (resolveFromProductionCaller openingsCall hash environment)
      rustObservation target = some targetEnvironment.acceptedCall.observation ∧
        ExactRustV5OpeningAndFriConsumerEquality sha256 rustObservation := by
  obtain ⟨targetEnvironment⟩ := hentry target haccepted
  refine ⟨targetEnvironment, ?_, ?_⟩
  · simp [AspisV5FriConsumerObservationBridge.observationFromAcceptedResolver,
      resolveFromProductionCaller]
  · exact production_caller_environment_implies_consumer_equality sha256 hash
      openingsCall
      (singleProductionCallerEnvironment openingsCall hash target
        targetEnvironment)
      hsource hhash

/-- Accepted-execution wrapper using the explicit Merkle call model.  The
former successful-call source equality is discharged internally. -/
theorem accepted_verifier_execution_builds_exact_production_caller_observation
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (verifierAccepts : AspisV5MerkleRustBridge.V5ProductionCall → Prop)
    (hentry : AcceptedVerifierExecutionBuildsProductionCallerEnvironment
      (AspisV5FriCallerMerkleBridge.exactMerkleOpeningCall hash) hash
      verifierAccepts)
    (hhash : AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
      sha256 hash)
    (target : AspisV5MerkleRustBridge.V5ProductionCall)
    (haccepted : verifierAccepts target) :
    ∃ targetEnvironment : ProductionCallerEnvironment
        (AspisV5FriCallerMerkleBridge.exactMerkleOpeningCall hash) hash target,
      let environment := singleProductionCallerEnvironment
        (AspisV5FriCallerMerkleBridge.exactMerkleOpeningCall hash) hash target
        targetEnvironment
      let rustObservation :=
        AspisV5FriConsumerObservationBridge.observationFromAcceptedResolver
          (resolveFromProductionCaller
            (AspisV5FriCallerMerkleBridge.exactMerkleOpeningCall hash) hash
            environment)
      rustObservation target = some targetEnvironment.acceptedCall.observation ∧
        ExactRustV5OpeningAndFriConsumerEquality sha256 rustObservation := by
  exact accepted_verifier_execution_builds_production_caller_observation
    sha256 hash (AspisV5FriCallerMerkleBridge.exactMerkleOpeningCall hash)
    verifierAccepts hentry
    (AspisV5FriCallerMerkleBridge.exactMerkleOpeningCall_sourceEquality hash)
    hhash target haccepted

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-- Released accepted-false event with the former abstract observation,
whole-consumer equality, and universal resolver premises replaced by one
accepted outer-verifier execution and the focused callback-wrapper edges. -/
theorem accepted_false_source_caller_event_with_released_tables
    {PointValue State : Type*}
    (rc : RoundConstants)
    {deployedOwner : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNote : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNullifier : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNode : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (hash : AspisV5MerkleUnchangedPublicAcceptanceBridge.GeneratedHash)
    (openingsCall : AspisV5FriCallerParametric.OpeningCall)
    (verifierAccepts : AspisV5MerkleRustBridge.V5ProductionCall → Prop)
    (hentry : AcceptedVerifierExecutionBuildsProductionCallerEnvironment
      openingsCall hash verifierAccepts)
    (hopeningSource :
      AspisV5FriCallerMerkleBridge.AcceptedCallerMerkleSourceEquality
        openingsCall hash)
    (hhash : AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
      sha256 hash)
    (rustCall : V5ProductionCall)
    (hverifierAccepted : verifierAccepts rustCall)
    (base : FixedSchedule (ZMod P) K)
    (hproduction : ProductionUsesReleasedFriTables base)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (causalFamily : CausalTranscriptFamily K)
    (input : SourceRelationInput K)
    (relationFamily : CoherentCandidateFamily K
      (AcceptedCandidate base causalFamily input))
    (records : CandidateRecords (AcceptedCandidate base causalFamily input) K)
    (statement : V5PublicStatement)
    (queries : QuerySchedule 18 131072)
    (decoder : OpeningFibreDecoder K)
    (expectedC2 : V5Query → Fin 4 → K)
    (transcriptInput : V5TranscriptInputs)
    (derived : V5DerivedValues K PointValue)
    (driverResult : V5TranscriptDriverResult K PointValue)
    (workFunctions : ExecutableWorkFunctions State
      (SqueezeResult K PointValue))
    (workInputs : PositionedWorkInputs State (SqueezeResult K PointValue))
    (hrelationSource : ∃ output,
      runSourceRelationVerifier input = some output)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode) :
    AspisV5AcceptedExecutionReleasedSecurity.ReleasedAcceptedExecutionSecurityEvent
    (¬ SourceRelationInputMatchesFamily input relationFamily)
    (¬ FamilyMatchesFriTranscript
      (concreteCodeEncoders base releasedEvaluationPoints)
      (acceptedTranscript causalFamily input) relationFamily input.challenges)
    (¬ TranscriptExecutionProjection input transcriptInput derived
      driverResult rustCall.queries queries)
    (¬ WorkExecutionProjection transcriptInput derived workInputs)
    (¬ ∃ reference : AcceptedV5Forest (sha256MerkleHashing sha256)
        rustCall.roots rustCall.queries,
      ForestProjectsToTranscript decoder (sha256MerkleHashing sha256)
        reference (acceptedTranscript causalFamily input) expectedC2)
    False
    (HashCollision (sha256MerkleHashing sha256))
    (¬ ExecutableWorkAcceptance workFunctions workInputs)
    (∃ forest : AcceptedV5Forest (sha256MerkleHashing sha256)
        rustCall.roots rustCall.queries,
      ¬ ForestFriChecks decoder (sha256MerkleHashing sha256) forest
        (acceptedSchedule base input)
        (acceptedTranscript causalFamily input) queries)
    (QueryPhaseFailure (acceptedSchedule base input)
      (acceptedTranscript causalFamily input) queries)
    (∃ (hfinal : FinalXMatchesReleasedDomain base)
        (htables : InverseTablesMatch base releasedEvaluationPoints)
        (hdecoding : PublishedOrdinaryPolynomialCurveDecoding (K := K)),
      (adaptiveBadSets base causalFamily hfinal htables hdecoding
        (constructedAdaptiveStrategies base causalFamily)).Occurs
        input.round0.alpha input.round1.alpha input.round2.alpha
          input.round3.alpha)
    (∃ candidate : AcceptedCandidate base causalFamily input,
      CandidateEarlierFailure rc (relationFamily.execution candidate)
        input.challenges statement (records candidate))
    (Fintype.card (AcceptedCandidate base causalFamily input) ≤ 240 ∧
      input.challenges ∈ boundedCandidateRepairEvent
        (fun candidate =>
          (relationFamily.execution candidate).adaptiveData))
    (¬ Poseidon2Faithful rc deployedOwner deployedNote deployedNullifier
      deployedNode) := by
  obtain ⟨targetEnvironment, hobservation, hconsumer⟩ :=
    accepted_verifier_execution_builds_production_caller_observation
      sha256 hash openingsCall verifierAccepts hentry hopeningSource hhash
      rustCall hverifierAccepted
  let environment := singleProductionCallerEnvironment openingsCall hash
    rustCall targetEnvironment
  let observation := targetEnvironment.acceptedCall.observation
  exact
    AspisV5AcceptedExecutionReleasedSecurity.accepted_false_source_observation_event_with_released_tables
      rc sha256
      (AspisV5FriConsumerObservationBridge.observationFromAcceptedResolver
        (resolveFromProductionCaller openingsCall hash environment))
      rustCall observation hconsumer hobservation base hproduction hpublished
      causalFamily input relationFamily records statement queries decoder
      expectedC2 transcriptInput derived driverResult workFunctions workInputs
      hrelationSource noWitness

#print axioms generatedRootsMatch_unique
#print axioms accepted_resolver_caller_implies_parser_output_equality
#print axioms accepted_resolver_caller_implies_consumer_equality
#print axioms resolveFromProductionCaller_uses_production_caller
#print axioms production_caller_environment_implies_consumer_equality
#print axioms exact_production_caller_environment_implies_consumer_equality
#print axioms accepted_verifier_execution_builds_production_caller_observation
#print axioms
  accepted_verifier_execution_builds_exact_production_caller_observation
#print axioms accepted_false_source_caller_event_with_released_tables

end AspisV5FriCallerAcceptedResolverBridge
