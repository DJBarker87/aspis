import AspisFormal.K1.V7Tag73FixedFieldMessageBridge
import AspisFormal.K1.V7Tag73SecureCircleMap
import AspisFormal.Pool.V7CompactSemanticBinding

/-!
# Exact Tag-73 semantic transcript bridge

This file instantiates the abstract Component-B `FiatShamirSchedule` with the
literal Tag-73 duplex and bounded sampler.  Its public prefix contains only
the random oracle and data available before C2; the C2 root is the separate
`maskRoot` field.  The semantic-round evaluator receives only the already
sent compact messages.  Consequently neither `eta` nor a round challenge can
inspect a later prover message.

The evaluator is total at the schedule interface and fail-closed internally:
an absent bounded decode maps to zero.  The acceptance bridge below does not
assume those defaults were taken.  It requires the exact executable replay to
return the recorded eta and ten recorded round challenges.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SemanticTranscriptBridge

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisSumcheckMasking
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCQM31Representation
open AspisV5ComponentCQM31TowerExact
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5SumcheckCommitment
open AspisV5SumcheckTranscriptBinding
open AspisV6TranscriptRelationGrammar
open AspisV6AcceptedPathObligations
open AspisPool.V7CompactSemanticBinding

/-! ## Incremental deployed challenge sampler -/

/-- Run the exact two-query duplex one block at a time, stopping at the first
prefix accepted by the deployed bounded decoder. -/
def sampleChallengeFrom (oracle : HashOracle) (id : ChallengeId) :
    Nat -> List Digest256 -> MachineState -> Option (Qm31Bytes × MachineState)
  | 0, _, _ => none
  | fuel + 1, outputs, state =>
      let squeezed := squeezeBlock oracle state
      let accumulated := outputs ++ [squeezed.1]
      match decodeChallengeParameter exactSecureCircleParameterMap id accumulated with
      | some value => some (value, squeezed.2)
      | none => sampleChallengeFrom oracle id fuel accumulated squeezed.2

/-- Exact deployed cap dispatch. -/
def sampleChallenge (oracle : HashOracle) (id : ChallengeId)
    (state : MachineState) : Option (Qm31Bytes × MachineState) :=
  sampleChallengeFrom oracle id (samplerBlockCap (samplerMode id)) [] state

/-- Decode the canonical Tag-73 bytes returned by the bounded sampler into
the exact mathematical QM31 tower. -/
def sampleExactChallenge (oracle : HashOracle) (id : ChallengeId)
    (state : MachineState) : Option (QM31Exact × MachineState) := do
  let (encoded, next) <- sampleChallenge oracle id state
  let value <- decodeTagQM31ExactLE encoded
  pure (value, next)

def sampleOnly (oracle : HashOracle) (id : ChallengeId)
    (state : MachineState) : Option MachineState := do
  let (_, next) <- sampleChallenge oracle id state
  pure next

def sampleIds (oracle : HashOracle) :
    List ChallengeId -> MachineState -> Option MachineState
  | [], state => some state
  | id :: rest, state => do
      let next <- sampleOnly oracle id state
      sampleIds oracle rest next

theorem sampleChallengeFrom_stops_at_first_success
    (oracle : HashOracle) (id : ChallengeId) (fuel : Nat)
    (prior : List Digest256) (state : MachineState)
    (value : Qm31Bytes) (next : MachineState)
    (run : sampleChallengeFrom oracle id fuel prior state = some (value, next)) :
    ∃ consumed : List Digest256,
      decodeChallengeParameter exactSecureCircleParameterMap id
          (prior ++ consumed) = some value ∧
      consumed ≠ [] ∧
      consumed.length ≤ fuel := by
  induction fuel generalizing prior state value next with
  | zero => simp [sampleChallengeFrom] at run
  | succ fuel ih =>
      simp only [sampleChallengeFrom] at run
      let squeezed := squeezeBlock oracle state
      let accumulated := prior ++ [squeezed.1]
      cases decoded : decodeChallengeParameter exactSecureCircleParameterMap id
          accumulated with
      | some decodedValue =>
          rw [decoded] at run
          have pairEq := Option.some.inj run
          cases pairEq
          refine ⟨[squeezed.1], ?_, by simp, by simp⟩
          simpa [accumulated] using decoded
      | none =>
          rw [decoded] at run
          have recursive :
              sampleChallengeFrom oracle id fuel accumulated squeezed.2 =
                some (value, next) := by
            simpa using run
          obtain ⟨tail, hdecode, hnonempty, hbound⟩ :=
            ih (prior := accumulated) (state := squeezed.2)
              (value := value) (next := next) recursive
          refine ⟨squeezed.1 :: tail, ?_, by simp, ?_⟩
          · simpa [accumulated, List.append_assoc] using hdecode
          · simp only [List.length_cons]
            omega

/-! ## Prefix which is genuinely available before eta -/

/-- Data available before the adaptive C2 root.  In particular it contains
no semantic-round message, point claim, terminal value, nonce, opening, or
query schedule. -/
structure SemanticPublicPrefix where
  oracle : HashOracle
  context : Context
  c1Root : Digest208
  initialClaim : Qm31Bytes

abbrev SemanticPreEta :=
  PreEtaTranscript SemanticPublicPrefix Digest208

def fixedPrefixBeforeC1 (publicData : SemanticPublicPrefix) : MachineState :=
  let state0 := absorb publicData.oracle initialState .profile
  let state1 := absorb publicData.oracle state0 .circleBasis
  let state2 := absorb publicData.oracle state1 (.deployment publicData.context)
  let state3 := absorb publicData.oracle state2
    (.statement publicData.context.statementDigest)
  absorb publicData.oracle state3 (.hidingPrecommit publicData.context)

/-- Replay exactly through the initial masked claim, stopping immediately
before the eta squeeze.  Both public-root salts use their deployed ASCII
domain and do not advance the duplex state. -/
def stateBeforeEta (preEta : SemanticPreEta) : Option MachineState := do
  let publicData := preEta.publicPrefix
  let beforeC1 := fixedPrefixBeforeC1 publicData
  let c1Salt := publicRootSalt publicData.oracle publicData.context c1TreeTag
  let afterC1 := absorb publicData.oracle beforeC1
    (.c1Root publicData.c1Root c1Salt)
  let afterLambda <- sampleOnly publicData.oracle .lambda afterC1
  let afterChi <- sampleOnly publicData.oracle .chi afterLambda
  let c2Salt := publicRootSalt publicData.oracle publicData.context c2TreeTag
  let afterC2 := absorb publicData.oracle afterChi
    (.c2Root preEta.maskRoot c2Salt)
  let afterRegistry := absorb publicData.oracle afterC2 .constraintRegistry
  let afterHelper := absorb publicData.oracle afterRegistry .helperSum
  let afterTheta <- sampleOnly publicData.oracle .theta afterHelper
  let afterPoint <- sampleIds publicData.oracle
    (List.ofFn fun coordinate : Fin 10 => .zerocheckPoint coordinate) afterTheta
  let afterMu <- sampleOnly publicData.oracle .mu afterPoint
  pure (absorb publicData.oracle afterMu
    (.initialMaskClaim publicData.initialClaim))

def runEta (preEta : SemanticPreEta) : Option (QM31Exact × MachineState) := do
  let state <- stateBeforeEta preEta
  sampleExactChallenge preEta.publicPrefix.oracle .eta state

/-! ## Exact compact semantic message encoding -/

/-- The inverse direction of the four-byte mathematical `u32` codec. -/
theorem encodeWordLE_decodeWordLE (wordBytes : WordBytes) :
    encodeWordLE (decodeWordLE wordBytes) = wordBytes := by
  have injective : Function.Injective encodeWordLE :=
    Function.LeftInverse.injective decodeWordLE_encodeWordLE
  have sameCard : Fintype.card RawWord = Fintype.card WordBytes := by
    simp [RawWord, WordBytes, rawWordCount]
  have surjective : Function.Surjective encodeWordLE :=
    ((Fintype.bijective_iff_injective_and_card encodeWordLE).2
      ⟨injective, sameCard⟩).2
  obtain ⟨word, encoded⟩ := surjective wordBytes
  rw [← encoded, decodeWordLE_encodeWordLE]

/-- Successful canonical four-limb decoding determines every input byte. -/
theorem encodeQM31LE_of_decodeQM31LE
    (encoded : AspisV5ComponentCQM31Representation.QM31Bytes)
    (limbs : QM31Limbs) (decoded : decodeQM31LE encoded = some limbs) :
    encodeQM31LE limbs = encoded := by
  unfold decodeQM31LE at decoded
  split at decoded
  next canonical =>
    have limbsEq := Option.some.inj decoded
    rw [← limbsEq]
    funext offset
    let position : Fin 4 × Fin 4 := finProdFinEquiv.symm offset
    have rawEq :
        m31AsRawWord
            ⟨decodeWordLE (qm31LimbBytes encoded position.1),
              canonical position.1⟩ =
          decodeWordLE (qm31LimbBytes encoded position.1) := by
      apply Fin.ext
      rfl
    change encodeM31LE
        ⟨decodeWordLE (qm31LimbBytes encoded position.1),
          canonical position.1⟩ position.2 = encoded offset
    rw [encodeM31LE, rawEq, encodeWordLE_decodeWordLE]
    change encoded (limbByteIndex position.1 position.2) = encoded offset
    congr 1
    exact (finProdFinEquiv (m := 4) (n := 4)).apply_symm_apply offset
  next noncanonical => simp at decoded

/-- A successful Tag-73 canonical decode round-trips to the literal runtime
bytes, not merely to an extension-field value with the same cardinality. -/
theorem encodeTagQM31ExactLE_of_decode
    (encoded : Qm31Bytes) (value : QM31Exact)
    (decoded : decodeTagQM31ExactLE encoded = some value) :
    encodeTagQM31ExactLE value = encoded := by
  unfold decodeTagQM31ExactLE at decoded
  unfold decodeQM31ExactLE at decoded
  cases lower : decodeQM31LE (tagQm31BytesToExact encoded) with
  | none => simp [lower] at decoded
  | some limbs =>
      rw [lower] at decoded
      have valueEq := Option.some.inj decoded
      rw [← valueEq]
      unfold encodeTagQM31ExactLE encodeQM31ExactLE
      rw [Equiv.symm_apply_apply]
      apply congrArg exactQm31BytesToTag
      exact encodeQM31LE_of_decodeQM31LE
        (tagQm31BytesToExact encoded) limbs lower

/-- Canonical decoding is injective on accepted Tag-73 byte strings. -/
theorem decodeTagQM31ExactLE_injective_on_success
    (left right : Qm31Bytes) (value : QM31Exact)
    (leftDecoded : decodeTagQM31ExactLE left = some value)
    (rightDecoded : decodeTagQM31ExactLE right = some value) :
    left = right := by
  rw [← encodeTagQM31ExactLE_of_decode left value leftDecoded,
    ← encodeTagQM31ExactLE_of_decode right value rightDecoded]

/-- The Tag-73 wire omits coefficient one.  Slot zero carries coefficient
zero; slots one through twenty-six carry coefficients two through twenty-seven. -/
def sentFieldsOfMessage (message : Degree27Message QM31Exact) :
    Fin 27 -> Qm31Bytes := fun sent =>
  if hzero : sent.val = 0 then
    encodeTagQM31ExactLE (message 0)
  else
    encodeTagQM31ExactLE (message <| (⟨sent.val + 1, by omega⟩ : Fin 28))

@[simp] theorem sentFieldsOfMessage_zero
    (message : Degree27Message QM31Exact) :
    sentFieldsOfMessage message 0 = encodeTagQM31ExactLE (message 0) := by
  rfl

theorem sentFieldsOfMessage_positive
    (message : Degree27Message QM31Exact) (sent : Fin 27)
    (positive : 0 < sent.val) :
    sentFieldsOfMessage message sent =
      encodeTagQM31ExactLE
        (message <| (⟨sent.val + 1, by omega⟩ : Fin 28)) := by
  simp [sentFieldsOfMessage, Nat.ne_of_gt positive]

theorem sentFieldsOfCompactMessage
    (fields : FixedFieldView QM31Exact)
    (point : Fin 10 -> QM31Exact)
    (round : Fin 10) :
    sentFieldsOfMessage (compactSemanticMessage fields point round) =
      fun sent => encodeTagQM31ExactLE (fields.semanticSent round sent) := by
  funext sent
  by_cases hzero : sent.val = 0
  · have sentEq : sent = 0 := Fin.ext hzero
    subst sent
    simp [sentFieldsOfMessage]
  · have positive : 0 < sent.val := Nat.pos_of_ne_zero hzero
    rw [sentFieldsOfMessage_positive _ sent positive]
    unfold compactSemanticMessage
    simp only [semanticCoefficient]
    rw [if_neg (by omega : sent.val + 1 ≠ 0)]
    rw [if_neg (by omega : sent.val + 1 ≠ 1)]
    simp only [semanticParts]
    congr 2
    apply Fin.ext
    simp
    omega

/-- The compact algebraic message serializes byte-for-byte as the accepted
raw Tag-73 semantic section. -/
theorem sentFieldsOfDecodedCompactMessage_eq_raw
    {raw : AspisK1.V7Tag73RawProverMessages.RawTag73ProverMessages}
    {decoded : Fin 641 -> QM31Exact}
    (decodeExact : FixedFieldDecodeExact raw decoded)
    (point : Fin 10 -> QM31Exact) (round : Fin 10) :
    sentFieldsOfMessage
        (compactSemanticMessage (decodedFixedFieldView decoded) point round) =
      raw.semanticSent round := by
  rw [sentFieldsOfCompactMessage]
  funext sent
  apply encodeTagQM31ExactLE_of_decode
  exact decode_semantic_of_fixedFieldDecodeExact decodeExact round sent

/-! ## Prefix-only semantic replay and schedule -/

def runSemanticMessages (oracle : HashOracle) :
    Nat -> List (Degree27Message QM31Exact) -> MachineState ->
      Option (List QM31Exact × MachineState)
  | _, [], state => some ([], state)
  | index, message :: rest, state =>
      if inRange : index < 10 then do
        let round : Fin 10 := ⟨index, inRange⟩
        let afterMessage := absorb oracle state
          (.semanticRound round (sentFieldsOfMessage message))
        let (challenge, afterChallenge) <-
          sampleExactChallenge oracle (.semantic round) afterMessage
        let (tail, finalState) <-
          runSemanticMessages oracle (index + 1) rest afterChallenge
        pure (challenge :: tail, finalState)
      else
        none

def runSemanticPrefix (preEta : SemanticPreEta) (eta : QM31Exact)
    (messages : List (Degree27Message QM31Exact)) :
    Option (List QM31Exact × MachineState) := do
  let (derivedEta, afterEta) <- runEta preEta
  if derivedEta = eta then
    runSemanticMessages preEta.publicPrefix.oracle 0 messages afterEta
  else
    none

def lastChallengeOrZero
    (result : Option (List QM31Exact × MachineState)) : QM31Exact :=
  match result with
  | some (values, _) => values.getLast?.getD 0
  | none => 0

/-- The literal Tag-73 semantic Fiat-Shamir schedule.  Its round input is a
list of already transmitted messages and nothing later. -/
def tag73SemanticSchedule :
    FiatShamirSchedule SemanticPublicPrefix Digest208 QM31Exact where
  eta := fun preEta =>
    match runEta preEta with
    | some (value, _) => value
    | none => 0
  roundChallenge := fun preEta eta messages =>
    lastChallengeOrZero (runSemanticPrefix preEta eta messages)

/-- Exact executable success data, suitable for projection from the
future-free verifier path.  This is a replay certificate, not an algebraic or
cryptographic assumption. -/
structure ExactSemanticReplay
    (preEta : SemanticPreEta) (eta : QM31Exact)
    (messages : Fin roundCount -> Degree27Message QM31Exact)
    (point : Fin roundCount -> QM31Exact) : Prop where
  etaRun : ∃ state, runEta preEta = some (eta, state)
  roundRun : ∀ round : Fin roundCount,
    ∃ state,
      runSemanticPrefix preEta eta
          (List.ofFn fun earlier : Fin (round.val + 1) =>
            messages ⟨earlier.val, by omega⟩) =
        some
          (List.ofFn (fun earlier : Fin (round.val + 1) =>
            point ⟨earlier.val, by omega⟩), state)

theorem exactSemanticReplay_eta_eq
    {preEta : SemanticPreEta} {eta : QM31Exact}
    {messages : Fin roundCount -> Degree27Message QM31Exact}
    {point : Fin roundCount -> QM31Exact}
    (replay : ExactSemanticReplay preEta eta messages point) :
    eta = tag73SemanticSchedule.eta preEta := by
  obtain ⟨state, run⟩ := replay.etaRun
  simp [tag73SemanticSchedule, run]

theorem exactSemanticReplay_point_eq
    {preEta : SemanticPreEta} {eta : QM31Exact}
    {messages : Fin roundCount -> Degree27Message QM31Exact}
    {point : Fin roundCount -> QM31Exact}
    (replay : ExactSemanticReplay preEta eta messages point) :
    point = derivedPoint tag73SemanticSchedule preEta eta messages := by
  funext round
  obtain ⟨state, run⟩ := replay.roundRun round
  simp only [derivedPoint, tag73SemanticSchedule, lastChallengeOrZero]
  rw [run]
  let values := List.ofFn (fun earlier : Fin (round.val + 1) =>
    point ⟨earlier.val, by omega⟩)
  have valuesNonempty : values ≠ [] := by
    simp [values]
  change point round = values.getLast?.getD 0
  rw [List.getLast?_eq_getLast_of_ne_nil valuesNonempty]
  simp only [Option.getD_some]
  unfold values
  rw [List.getLast_ofFn_succ]
  congr 1

/-- An exact future-free semantic replay constructs the concrete accepted-run
object consumed by K1.5. -/
def acceptedRunOfExactSemanticReplay
    {preEta : SemanticPreEta} {eta : QM31Exact}
    {messages : Fin roundCount -> Degree27Message QM31Exact}
    {point : Fin roundCount -> QM31Exact}
    (replay : ExactSemanticReplay preEta eta messages point) :
    AcceptedRun tag73SemanticSchedule where
  preEta := preEta
  eta := eta
  messages := messages
  point := point
  eta_eq := exactSemanticReplay_eta_eq replay
  point_eq := exactSemanticReplay_point_eq replay

#print axioms sampleChallengeFrom_stops_at_first_success
#print axioms encodeQM31LE_of_decodeQM31LE
#print axioms encodeTagQM31ExactLE_of_decode
#print axioms decodeTagQM31ExactLE_injective_on_success
#print axioms sentFieldsOfCompactMessage
#print axioms sentFieldsOfDecodedCompactMessage_eq_raw
#print axioms exactSemanticReplay_eta_eq
#print axioms exactSemanticReplay_point_eq
#print axioms acceptedRunOfExactSemanticReplay

end AspisK1.V7Tag73SemanticTranscriptBridge
