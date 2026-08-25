import Mathlib

/-!
# Exact deployed Tag-73 transcript schedule

This file is a typed, byte-length-exact model of the transcript used by the
deployed V7 verifier.  It deliberately separates three things that are easy to
conflate:

* transcript absorption/squeezing;
* prover grinding queries, which do not advance the transcript state; and
* the verifier's branched, first-success query-schedule scan.

The model does not assert that SHA-256 is collision resistant or a random
oracle.  `HashOracle` is an explicit parameter.  The theorems below identify
the exact oracle input at every state transition; computational binding of two
different inputs remains the allowed SHA-256/random-oracle boundary.

`Messages.challengeValue` records the value returned by the deployed bounded
decoder, while `SamplerUse` records its exact number of raw duplex blocks.
Coupling those values to the bit-level Rust rejection samplers is intentionally
the named sampler component of the K1.6 trace-cover lemma; it is not smuggled
in here as a field asserting random-oracle uniformity.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73TranscriptSchedule

abbrev Bytes (n : Nat) := Fin n → UInt8
abbrev Digest256 := Bytes 32
abbrev Digest208 := Bytes 26
abbrev Qm31Bytes := Bytes 16
abbrev NonceBytes := Bytes 8
abbrev ByteString := List UInt8

def bytes {n : Nat} (value : Bytes n) : ByteString :=
  List.ofFn value

def zeroBytes (n : Nat) : Bytes n := fun _ => 0

def encodeBlocks {count width : Nat} (values : Fin count → Bytes width) : ByteString :=
  (List.ofFn values).flatMap bytes

def encodeMatrix {rows columns width : Nat}
    (values : Fin rows → Fin columns → Bytes width) : ByteString :=
  (List.ofFn fun row => encodeBlocks (values row)).flatten

@[simp] theorem bytes_length {n : Nat} (value : Bytes n) :
    (bytes value).length = n := by
  exact List.length_ofFn

@[simp] theorem encodeBlocks_length {count width : Nat}
    (values : Fin count → Bytes width) :
    (encodeBlocks values).length = count * width := by
  simp only [encodeBlocks, List.length_flatMap, bytes_length,
    List.map_const', List.length_ofFn, List.sum_replicate_nat]

@[simp] theorem encodeMatrix_length {rows columns width : Nat}
    (values : Fin rows → Fin columns → Bytes width) :
    (encodeMatrix values).length = rows * (columns * width) := by
  simp only [encodeMatrix, List.length_flatten]
  rw [List.map_ofFn]
  simp only [Function.comp_apply, encodeBlocks_length, List.sum_ofFn]
  simp

/-! ## Frozen deployment and transcript constants -/

def profileBinding : ByteString :=
  [65, 86, 55, 79, 70, 48, 48, 49,
   26, 3, 10, 16, 203, 0, 26, 32,
   27, 4, 6, 35, 31, 34, 113, 241,
   129, 2, 8, 20, 18, 1, 64, 1]

def circleBasisBinding : ByteString :=
  [97, 115, 112, 105, 115, 58, 99, 49, 58, 109, 51,
   49, 45, 99, 105, 114, 99, 108, 101, 58, 118, 48]

def publicRootSaltDomain : ByteString :=
  [97, 115, 112, 105, 115, 45, 118, 55, 45, 112, 117, 98, 108, 105,
   99, 45, 114, 111, 111, 116, 45, 115, 97, 108, 116, 45, 118, 49]

def maskLayoutFingerprintLe : ByteString :=
  [153, 204, 22, 24, 64, 189, 218, 15]

def spendLayoutFactorFingerprintLe : ByteString :=
  [2, 221, 76, 44, 80, 138, 254, 16]

def stateOnlyRegistry : ByteString :=
  [1, 29, 95, 0, 10, 27, 28, 102, 0, 17,
   48, 33, 175, 20, 236, 180, 29, 18,
   251, 234, 229, 239, 81, 34, 103, 18,
   0, 0]

theorem frozen_record_lengths :
    profileBinding.length = 32 ∧
    circleBasisBinding.length = 22 ∧
    publicRootSaltDomain.length = 28 ∧
    stateOnlyRegistry.length = 28 := by
  decide

def profileLabel : UInt8 := 1
def statementLabel : UInt8 := 2
def finalWorkNonceLabel : UInt8 := 5
def circleBasisLabel : UInt8 := 11
def c1RootLabel : UInt8 := 12
def c2RootLabel : UInt8 := 13
def foldWorkNonceLabel : UInt8 := 20
def batchWorkNonceLabel : UInt8 := 28
def hidingPrecommitLabel : UInt8 := 30
def initialMaskClaimLabel : UInt8 := 31
def constraintRegistryLabel : UInt8 := 32
def helperSumLabel : UInt8 := 33
def semanticRoundLabel : UInt8 := 48
def pointClaimsLabel : UInt8 := 49
def inactiveClaimLabel : UInt8 := 50
def circleOodValueLabel : UInt8 := 51
def relationRoundLabel : UInt8 := 52
def final256Label : UInt8 := 53
def queryCandidateLabel : UInt8 := 57
def queryBatchChallengeLabel : UInt8 := 58
def queryBatchClaimLabel : UInt8 := 59
def deploymentLabel : UInt8 := 60

def domAbsorb : UInt8 := 0
def domSqueeze : UInt8 := 1
def domAdvance : UInt8 := 2
def domGrind : UInt8 := 3

def c1TreeTag : UInt8 := 113
def c2TreeTag : UInt8 := 241

/-! ## Context and challenge-dependent messages -/

structure Context where
  programId : Bytes 32
  releaseBinding : Bytes 32
  statementDigest : Bytes 32
  /-- The production value is the proof-account public key. -/
  attemptId : Bytes 32

def hidingPrecommitBytes (context : Context) : ByteString :=
  [1] ++ bytes context.statementDigest ++ bytes context.attemptId ++
    maskLayoutFingerprintLe ++ spendLayoutFactorFingerprintLe

def deploymentBytes (context : Context) : ByteString :=
  bytes context.programId ++ bytes context.releaseBinding

def rootSaltInput (context : Context) (treeTag : UInt8) : ByteString :=
  publicRootSaltDomain ++ profileBinding ++ bytes context.programId ++
    bytes context.releaseBinding ++ bytes context.statementDigest ++
    bytes context.attemptId ++ [treeTag]

theorem hiding_precommit_length (context : Context) :
    (hidingPrecommitBytes context).length = 81 := by
  simp [hidingPrecommitBytes, maskLayoutFingerprintLe,
    spendLayoutFactorFingerprintLe]

theorem root_salt_input_length (context : Context) (treeTag : UInt8) :
    (rootSaltInput context treeTag).length = 189 := by
  simp only [rootSaltInput, List.length_append, bytes_length,
    List.length_cons, List.length_nil]
  norm_num [publicRootSaltDomain, profileBinding]

structure HashOracle where
  answer : ByteString → Digest256

def publicRootSalt (oracle : HashOracle) (context : Context)
    (treeTag : UInt8) : Digest256 :=
  oracle.answer (rootSaltInput context treeTag)

inductive ChallengeId where
  | lambda
  | chi
  | theta
  | zerocheckPoint (coordinate : Fin 10)
  | mu
  | eta
  | semantic (round : Fin 10)
  | gamma
  | kappa
  | circlePoint (sample : Fin 2)
  | oodMix (sample : Fin 2)
  | alpha (round : Fin 4)
  | queryBatch
  deriving DecidableEq, Repr

inductive SamplerMode where
  | ordinaryQm31
  | nonzeroQm31
  | secureCirclePoint
  deriving DecidableEq, Repr

def samplerMode : ChallengeId → SamplerMode
  | .eta | .gamma | .kappa | .queryBatch => .nonzeroQm31
  | .circlePoint _ => .secureCirclePoint
  | _ => .ordinaryQm31

def samplerBlockCap : SamplerMode → Nat
  | .ordinaryQm31 => 4
  | .nonzeroQm31 => 12
  | .secureCirclePoint => 12

/-- The number of 32-byte duplex blocks actually consumed is part of an
execution.  It is not silently replaced by the one-block common case. -/
structure SamplerUse (id : ChallengeId) where
  blocksUsed : Nat
  consumesBlock : 0 < blocksUsed
  withinDeployedCap : blocksUsed ≤ samplerBlockCap (samplerMode id)

/-- `C2Commitment` can only be constructed at the type indexed by the decoded
`lambda` and `chi` recorded after C1.  This records the deployed adaptive C2
boundary without asserting any algebraic property of C2 or the missing raw
sampler coupling. -/
structure C2Commitment (lambda chi : Qm31Bytes) where
  root : Digest208

inductive WorkStage where
  | batch
  | fold
  | final
  deriving DecidableEq, Repr

def workBits : WorkStage → Nat
  | .batch => 35
  | .fold => 31
  | .final => 34

/-- The adversary may test any list of nonces at this stage and select any
satisfying nonce.  In contrast to q16 selection, there is no first-success
nonce condition in the deployed verifier. -/
structure GrindingChoice (stage : WorkStage) where
  probesBeforeSelected : List NonceBytes
  selected : NonceBytes

inductive RetryPolicy where
  | arbitrarySatisfyingNonce (bits : Nat)
  | firstCap203Counter (candidateCap frontierCap : Nat)
  deriving DecidableEq, Repr

def retryPolicy : WorkStage → RetryPolicy
  | .batch => .arbitrarySatisfyingNonce 35
  | .fold => .arbitrarySatisfyingNonce 31
  | .final => .arbitrarySatisfyingNonce 34

theorem three_work_stages_are_distinct :
    workBits .batch = 35 ∧ workBits .fold = 31 ∧ workBits .final = 34 := by
  decide

theorem no_work_stage_has_first_success_policy (stage : WorkStage) :
    ∃ bits, retryPolicy stage = .arbitrarySatisfyingNonce bits := by
  cases stage <;> simp [retryPolicy]

/-! ## Exact absorbed records -/

inductive Payload where
  | profile
  | circleBasis
  | deployment (context : Context)
  | statement (digest : Digest256)
  | hidingPrecommit (context : Context)
  | c1Root (root : Digest208) (salt : Digest256)
  | c2Root (root : Digest208) (salt : Digest256)
  | constraintRegistry
  | helperSum
  | initialMaskClaim (claim : Qm31Bytes)
  | semanticRound (round : Fin 10) (sent : Fin 27 → Qm31Bytes)
  | pointClaims (claims : Fin 3 → Fin 29 → Qm31Bytes)
  | batchNonce (nonce : NonceBytes)
  | inactiveClaim (claim : Qm31Bytes)
  | circleOodValue (sample : Fin 2) (value : Qm31Bytes)
  | relationRound (round : Fin 4) (sent : Fin 6 → Qm31Bytes)
  | foldNonce (nonce : NonceBytes)
  | final256 (values : Fin 256 → Qm31Bytes)
  | finalNonce (nonce : NonceBytes)
  | queryCandidate (counter : Fin 64)
  | queryBatchDomain
  | queryBatchClaim (claim : Qm31Bytes)

def Payload.label : Payload → UInt8
  | .profile => profileLabel
  | .circleBasis => circleBasisLabel
  | .deployment _ => deploymentLabel
  | .statement _ => statementLabel
  | .hidingPrecommit _ => hidingPrecommitLabel
  | .c1Root _ _ => c1RootLabel
  | .c2Root _ _ => c2RootLabel
  | .constraintRegistry => constraintRegistryLabel
  | .helperSum => helperSumLabel
  | .initialMaskClaim _ => initialMaskClaimLabel
  | .semanticRound _ _ => semanticRoundLabel
  | .pointClaims _ => pointClaimsLabel
  | .batchNonce _ => batchWorkNonceLabel
  | .inactiveClaim _ => inactiveClaimLabel
  | .circleOodValue _ _ => circleOodValueLabel
  | .relationRound _ _ => relationRoundLabel
  | .foldNonce _ => foldWorkNonceLabel
  | .final256 _ => final256Label
  | .finalNonce _ => finalWorkNonceLabel
  | .queryCandidate _ => queryCandidateLabel
  | .queryBatchDomain => queryBatchChallengeLabel
  | .queryBatchClaim _ => queryBatchClaimLabel

def Payload.data : Payload → ByteString
  | .profile => profileBinding
  | .circleBasis => circleBasisBinding
  | .deployment context => deploymentBytes context
  | .statement digest => bytes digest
  | .hidingPrecommit context => hidingPrecommitBytes context
  | .c1Root root salt => [0] ++ bytes root ++ bytes salt
  | .c2Root root salt => bytes root ++ bytes salt
  | .constraintRegistry => stateOnlyRegistry
  | .helperSum => List.replicate 16 0
  | .initialMaskClaim claim => [27, 10] ++ bytes claim
  | .semanticRound round sent => [UInt8.ofNat round.val] ++ encodeBlocks sent
  | .pointClaims claims => encodeMatrix claims
  | .batchNonce nonce => bytes nonce
  | .inactiveClaim claim => bytes claim
  | .circleOodValue sample value => [UInt8.ofNat sample.val] ++ bytes value
  | .relationRound round sent => [UInt8.ofNat round.val] ++ encodeBlocks sent
  | .foldNonce nonce => [0] ++ bytes nonce
  | .final256 values => encodeBlocks values
  | .finalNonce nonce => bytes nonce
  | .queryCandidate counter => [UInt8.ofNat counter.val]
  | .queryBatchDomain => []
  | .queryBatchClaim claim => bytes claim

theorem payload_lengths
    (context : Context) (root : Digest208) (salt : Digest256)
    (claim : Qm31Bytes) (semantic : Fin 27 → Qm31Bytes)
    (points : Fin 3 → Fin 29 → Qm31Bytes)
    (relation : Fin 6 → Qm31Bytes) (finalValues : Fin 256 → Qm31Bytes)
    (nonce : NonceBytes) :
    (Payload.c1Root root salt).data.length = 59 ∧
    (Payload.c2Root root salt).data.length = 58 ∧
    (Payload.initialMaskClaim claim).data.length = 18 ∧
    (Payload.semanticRound 0 semantic).data.length = 433 ∧
    (Payload.pointClaims points).data.length = 1392 ∧
    (Payload.relationRound 0 relation).data.length = 97 ∧
    (Payload.final256 finalValues).data.length = 4096 ∧
    (Payload.foldNonce nonce).data.length = 9 ∧
    (Payload.hidingPrecommit context).data.length = 81 := by
  simp only [Payload.data, List.length_append, List.length_cons,
    List.length_nil, bytes_length, encodeBlocks_length, encodeMatrix_length,
    hiding_precommit_length]
  norm_num

/-! ## Duplex execution and exact challenge binding -/

structure OracleQuery where
  input : ByteString
  output : Digest256

structure MachineState where
  digest : Digest256
  oracleHistory : List OracleQuery

def initialState : MachineState where
  digest := zeroBytes 32
  oracleHistory := []

def absorbInput (state : MachineState) (payload : Payload) : ByteString :=
  bytes state.digest ++ [domAbsorb, payload.label] ++ payload.data

def absorb (oracle : HashOracle) (state : MachineState)
    (payload : Payload) : MachineState :=
  let input := absorbInput state payload
  let output := oracle.answer input
  { digest := output
    oracleHistory := state.oracleHistory ++ [{ input, output }] }

def squeezeOutputInput (state : MachineState) : ByteString :=
  bytes state.digest ++ [domSqueeze]

def squeezeAdvanceInput (state : MachineState) : ByteString :=
  bytes state.digest ++ [domAdvance]

def squeezeBlock (oracle : HashOracle) (state : MachineState) :
    Digest256 × MachineState :=
  let outputInput := squeezeOutputInput state
  let output := oracle.answer outputInput
  let advanceInput := squeezeAdvanceInput state
  let advanced := oracle.answer advanceInput
  (output,
    { digest := advanced
      oracleHistory := state.oracleHistory ++
        [{ input := outputInput, output }, { input := advanceInput, output := advanced }] })

def squeezeBlocks (oracle : HashOracle) : Nat → MachineState →
    List Digest256 × MachineState
  | 0, state => ([], state)
  | count + 1, state =>
      let first := squeezeBlock oracle state
      let rest := squeezeBlocks oracle count first.2
      (first.1 :: rest.1, rest.2)

def grindInput (state : MachineState) (nonce : NonceBytes) : ByteString :=
  bytes state.digest ++ [domGrind] ++ bytes nonce

def recordGrindingQuery (oracle : HashOracle) (state : MachineState)
    (nonce : NonceBytes) : MachineState :=
  let input := grindInput state nonce
  let output := oracle.answer input
  { state with oracleHistory := state.oracleHistory ++ [{ input, output }] }

theorem absorb_binds_exact_previous_state (oracle : HashOracle)
    (state : MachineState) (payload : Payload) :
    (absorb oracle state payload).digest =
      oracle.answer (bytes state.digest ++ [0, payload.label] ++ payload.data) := by
  rfl

theorem squeeze_binds_exact_previous_state (oracle : HashOracle)
    (state : MachineState) :
    (squeezeBlock oracle state).1 =
      oracle.answer (bytes state.digest ++ [1]) ∧
    (squeezeBlock oracle state).2.digest =
      oracle.answer (bytes state.digest ++ [2]) := by
  exact ⟨rfl, rfl⟩

theorem grinding_does_not_advance_transcript (oracle : HashOracle)
    (state : MachineState) (nonce : NonceBytes) :
    (recordGrindingQuery oracle state nonce).digest = state.digest := by
  rfl

inductive Checkpoint where
  | canonicalWire
  | semanticTerminal
  | batchWork
  | foldWork
  | finalWork
  | frontierCount
  | twoTreeAuthentication
  | relationTerminal
  deriving DecidableEq, Repr

inductive MachineEvent where
  | absorb (payload : Payload)
  | challenge (id : ChallengeId) (use : SamplerUse id)
  | grind (stage : WorkStage) (choice : GrindingChoice stage)
  | check (checkpoint : Checkpoint)

def executeEvent (oracle : HashOracle) (state : MachineState) :
    MachineEvent → MachineState
  | .absorb payload => absorb oracle state payload
  | .challenge _ use => (squeezeBlocks oracle use.blocksUsed state).2
  | .grind _ choice =>
      (choice.probesBeforeSelected.foldl
        (recordGrindingQuery oracle) state |> fun queried =>
          recordGrindingQuery oracle queried choice.selected)
  | .check _ => state

def run (oracle : HashOracle) : List MachineEvent → MachineState → MachineState
  | [], state => state
  | event :: rest, state => run oracle rest (executeEvent oracle state event)

def stateBefore (oracle : HashOracle) (start : MachineState)
    (events : List MachineEvent) (index : Nat) : MachineState :=
  run oracle (events.take index) start

def firstChallengeOracleInputAt (oracle : HashOracle) (start : MachineState)
    (events : List MachineEvent) (index : Nat) : ByteString :=
  squeezeOutputInput (stateBefore oracle start events index)

/-- Every challenge begins by hashing the state obtained from exactly the
preceding event prefix.  Rejection retries merely consume later squeeze blocks
from that same chain. -/
theorem every_challenge_binds_exact_preceding_prefix
    (oracle : HashOracle) (start : MachineState) (events : List MachineEvent)
    (index : Nat) (id : ChallengeId) (use : SamplerUse id)
    (_atIndex : events[index]? = some (MachineEvent.challenge id use)) :
    firstChallengeOracleInputAt oracle start events index =
      bytes (run oracle (events.take index) start).digest ++ [domSqueeze] := by
  rfl

/-! ## Full linear schedule around the branched q16 scan -/

structure Messages where
  context : Context
  challengeValue : ChallengeId → Qm31Bytes
  challengeUse : (id : ChallengeId) → SamplerUse id
  c1Root : Digest208
  c2 : C2Commitment (challengeValue .lambda) (challengeValue .chi)
  initialClaim : Qm31Bytes
  semanticSent : Fin 10 → Fin 27 → Qm31Bytes
  pointClaims : Fin 3 → Fin 29 → Qm31Bytes
  batchGrinding : GrindingChoice .batch
  inactiveClaim : Qm31Bytes
  oodValue : Fin 2 → Qm31Bytes
  relationSent : Fin 4 → Fin 6 → Qm31Bytes
  foldGrinding : GrindingChoice .fold
  finalValues : Fin 256 → Qm31Bytes
  finalGrinding : GrindingChoice .final
  queryBatchClaim : Qm31Bytes

def challengeEvent (messages : Messages) (id : ChallengeId) : MachineEvent :=
  .challenge id (messages.challengeUse id)

def semanticEvents (messages : Messages) : List MachineEvent :=
  (List.ofFn fun round : Fin 10 =>
    [.absorb (.semanticRound round (messages.semanticSent round)),
     challengeEvent messages (.semantic round)]).flatten

def oodEvents (messages : Messages) : List MachineEvent :=
  (List.ofFn fun sample : Fin 2 =>
    [challengeEvent messages (.circlePoint sample),
     .absorb (.circleOodValue sample (messages.oodValue sample)),
     challengeEvent messages (.oodMix sample)]).flatten

def relationTailEvents (messages : Messages) : List MachineEvent :=
  (List.ofFn fun tail : Fin 3 =>
    let round : Fin 4 := ⟨tail.val + 1, by omega⟩
    [.absorb (.relationRound round (messages.relationSent round)),
     challengeEvent messages (.alpha round)]).flatten

def beforeQueryScan (oracle : HashOracle) (messages : Messages) : List MachineEvent :=
  let context := messages.context
  let c1Salt := publicRootSalt oracle context c1TreeTag
  let c2Salt := publicRootSalt oracle context c2TreeTag
  [.check .canonicalWire,
   .absorb .profile,
   .absorb .circleBasis,
   .absorb (.deployment context),
   .absorb (.statement context.statementDigest),
   .absorb (.hidingPrecommit context),
   .absorb (.c1Root messages.c1Root c1Salt),
   challengeEvent messages .lambda,
   challengeEvent messages .chi,
   .absorb (.c2Root messages.c2.root c2Salt),
   .absorb .constraintRegistry,
   .absorb .helperSum,
   challengeEvent messages .theta] ++
  (List.ofFn fun coordinate : Fin 10 =>
    challengeEvent messages (.zerocheckPoint coordinate)) ++
  [challengeEvent messages .mu,
   .absorb (.initialMaskClaim messages.initialClaim),
   challengeEvent messages .eta] ++
  semanticEvents messages ++
  [.absorb (.pointClaims messages.pointClaims),
   .check .semanticTerminal,
   .grind .batch messages.batchGrinding,
   .check .batchWork,
   .absorb (.batchNonce messages.batchGrinding.selected),
   challengeEvent messages .gamma,
   .absorb (.inactiveClaim messages.inactiveClaim),
   challengeEvent messages .kappa] ++
  oodEvents messages ++
  [.absorb (.relationRound 0 (messages.relationSent 0)),
   .grind .fold messages.foldGrinding,
   .check .foldWork,
   .absorb (.foldNonce messages.foldGrinding.selected),
   challengeEvent messages (.alpha 0),
   .absorb (.final256 messages.finalValues),
   .grind .final messages.finalGrinding,
   .check .finalWork,
   .absorb (.finalNonce messages.finalGrinding.selected)]

def afterAcceptedQueryScan (messages : Messages) : List MachineEvent :=
  [.check .frontierCount,
   .absorb .queryBatchDomain,
   challengeEvent messages .queryBatch,
   .check .twoTreeAuthentication,
   .absorb (.queryBatchClaim messages.queryBatchClaim)] ++
  relationTailEvents messages ++ [.check .relationTerminal]

theorem c2_occurs_after_lambda_and_chi (oracle : HashOracle)
    (messages : Messages) :
    ((beforeQueryScan oracle messages).take 10)[7]? =
        some (challengeEvent messages .lambda) ∧
    ((beforeQueryScan oracle messages).take 10)[8]? =
        some (challengeEvent messages .chi) ∧
    ((beforeQueryScan oracle messages).take 10)[9]? =
        some (MachineEvent.absorb (.c2Root messages.c2.root
          (publicRootSalt oracle messages.context c2TreeTag))) := by
  simp [beforeQueryScan]

/-! ## First-success, cap-203 q16 schedule -/

structure QuerySchedule where
  positions : Fin 16 ↪ Fin (2 ^ 18)
  blocksUsed : Nat
  atLeastTwoBlocks : 2 ≤ blocksUsed
  withinSixtyFourDraws : blocksUsed ≤ 8

inductive CandidateOutcome where
  | samplerAbort
  | schedule (value : QuerySchedule)

/-- A q16 sampler abort means that all sixty-four four-limb draw attempts were
consumed, i.e. all eight 32-byte duplex blocks. -/
def CandidateOutcome.blocksUsed : CandidateOutcome → Nat
  | .samplerAbort => 8
  | .schedule value => value.blocksUsed

/-- `frontierNodes` is the exact binary-frontier recurrence supplied by the
query-graph component.  An accepting scan cannot skip a sampler abort. -/
structure FirstCap203Search (frontierNodes : QuerySchedule → Nat) where
  outcome : Fin 64 → CandidateOutcome
  selectedCounter : Fin 64
  selectedSchedule : QuerySchedule
  selectedOutcome : outcome selectedCounter = .schedule selectedSchedule
  selectedCompact : frontierNodes selectedSchedule ≤ 203
  everyEarlierSampledAndNoncompact : ∀ counter,
    counter.val < selectedCounter.val →
      ∃ schedule,
        outcome counter = .schedule schedule ∧ 203 < frontierNodes schedule

theorem selected_counter_is_first_cap203
    (frontierNodes : QuerySchedule → Nat)
    (search : FirstCap203Search frontierNodes) (counter : Fin 64)
    (earlier : counter.val < search.selectedCounter.val) :
    ∃ schedule,
      search.outcome counter = .schedule schedule ∧
      ¬ frontierNodes schedule ≤ 203 := by
  obtain ⟨schedule, hschedule, hlarge⟩ :=
    search.everyEarlierSampledAndNoncompact counter earlier
  exact ⟨schedule, hschedule, Nat.not_le_of_lt hlarge⟩

def candidateAbsorbInput (base : MachineState) (counter : Fin 64) : ByteString :=
  bytes base.digest ++ [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val]

/-- Each candidate is evaluated from a separate clone of the post-final-nonce
state.  Its candidate label is absorbed and its bounded without-replacement
sampler then consumes the recorded number of duplex blocks. -/
def runCandidateBranch (oracle : HashOracle) (base : MachineState)
    (counter : Fin 64) (outcome : CandidateOutcome) : MachineState :=
  let candidateState := absorb oracle base (.queryCandidate counter)
  (squeezeBlocks oracle outcome.blocksUsed candidateState).2

def postFinalNonceState (oracle : HashOracle) (messages : Messages) : MachineState :=
  run oracle (beforeQueryScan oracle messages) initialState

/-- Only the selected candidate branch becomes the continuing transcript. -/
def selectedCandidateState (oracle : HashOracle) (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) : MachineState :=
  runCandidateBranch oracle (postFinalNonceState oracle messages)
    search.selectedCounter (.schedule search.selectedSchedule)

/-- Full accepted linear transcript after resolving the verifier's branched
q16 scan.  Earlier failed branches remain oracle queries but are not chained
into this state. -/
def acceptedTranscriptState (oracle : HashOracle) (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) : MachineState :=
  run oracle (afterAcceptedQueryScan messages)
    (selectedCandidateState oracle messages search)

/-- Every counter candidate is cloned from the same post-final-nonce state;
failed frontier candidates are not chained into the accepted transcript. -/
theorem candidate_branches_share_one_base (base : MachineState)
    (first second : Fin 64) :
    candidateAbsorbInput base first =
        bytes base.digest ++ [0, 57, UInt8.ofNat first.val] ∧
    candidateAbsorbInput base second =
        bytes base.digest ++ [0, 57, UInt8.ofNat second.val] := by
  exact ⟨rfl, rfl⟩

theorem selected_candidate_uses_recorded_sampler_blocks
    (oracle : HashOracle) (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    selectedCandidateState oracle messages search =
      (squeezeBlocks oracle search.selectedSchedule.blocksUsed
        (absorb oracle (postFinalNonceState oracle messages)
          (.queryCandidate search.selectedCounter))).2 := by
  rfl

theorem query_batch_challenge_binds_selected_candidate_branch
    (oracle : HashOracle) (messages : Messages)
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    firstChallengeOracleInputAt oracle
        (selectedCandidateState oracle messages search)
        (afterAcceptedQueryScan messages) 2 =
      bytes (run oracle ((afterAcceptedQueryScan messages).take 2)
        (selectedCandidateState oracle messages search)).digest ++ [domSqueeze] := by
  rfl

/-! ## Exact terminal acceptance shape -/

/-- The deployed query equality is one degree-at-most-15 residual evaluated
at the nonzero query-batch challenge.  It is not a conjunction of sixteen
pointwise equalities. -/
def BatchedQueryResidualZero
    (Residual : Type*) (evaluateAt : Residual → Qm31Bytes → Qm31Bytes)
    (zero : Qm31Bytes) (residual : Residual) (rho : Qm31Bytes) : Prop :=
  evaluateAt residual rho = zero

structure AcceptanceFacts
    (frontierNodes : QuerySchedule → Nat)
    (Residual : Type*) (evaluateAt : Residual → Qm31Bytes → Qm31Bytes)
    (zero : Qm31Bytes) (messages : Messages) where
  canonicalFixedAndOpeningLimbs : Prop
  exactSemanticTerminal : Prop
  batchWork35Accepted : Prop
  foldWork31Accepted : Prop
  finalWork34Accepted : Prop
  querySearch : FirstCap203Search frontierNodes
  instructionFrontierMatches : Prop
  bothTypedTreesAuthenticate : Prop
  residual : Residual
  residualDegreeAtMost15 : Prop
  allFourRelationBoundaries : Prop
  finalDotProductTerminal : Prop

def Accepts
    {frontierNodes : QuerySchedule → Nat}
    {Residual : Type*} {evaluateAt : Residual → Qm31Bytes → Qm31Bytes}
    {zero : Qm31Bytes} {messages : Messages}
    (facts : AcceptanceFacts frontierNodes Residual evaluateAt zero messages) : Prop :=
  facts.canonicalFixedAndOpeningLimbs ∧
  facts.exactSemanticTerminal ∧
  facts.batchWork35Accepted ∧
  facts.foldWork31Accepted ∧
  facts.finalWork34Accepted ∧
  facts.instructionFrontierMatches ∧
  facts.bothTypedTreesAuthenticate ∧
  facts.residualDegreeAtMost15 ∧
  BatchedQueryResidualZero Residual evaluateAt zero facts.residual
    (messages.challengeValue .queryBatch) ∧
  facts.allFourRelationBoundaries ∧
  facts.finalDotProductTerminal

theorem accepts_implies_batched_not_pointwise_claim
    {frontierNodes : QuerySchedule → Nat}
    {Residual : Type*} {evaluateAt : Residual → Qm31Bytes → Qm31Bytes}
    {zero : Qm31Bytes} {messages : Messages}
    (facts : AcceptanceFacts frontierNodes Residual evaluateAt zero messages)
    (accepted : Accepts facts) :
    evaluateAt facts.residual (messages.challengeValue .queryBatch) = zero := by
  exact accepted.2.2.2.2.2.2.2.2.1

#print axioms frozen_record_lengths
#print axioms hiding_precommit_length
#print axioms root_salt_input_length
#print axioms payload_lengths
#print axioms three_work_stages_are_distinct
#print axioms no_work_stage_has_first_success_policy
#print axioms absorb_binds_exact_previous_state
#print axioms squeeze_binds_exact_previous_state
#print axioms grinding_does_not_advance_transcript
#print axioms every_challenge_binds_exact_preceding_prefix
#print axioms c2_occurs_after_lambda_and_chi
#print axioms selected_counter_is_first_cap203
#print axioms candidate_branches_share_one_base
#print axioms selected_candidate_uses_recorded_sampler_blocks
#print axioms query_batch_challenge_binds_selected_candidate_branch
#print axioms accepts_implies_batched_not_pointwise_claim

end AspisK1.V7Tag73TranscriptSchedule
