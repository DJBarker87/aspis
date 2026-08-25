import AspisFormal.K1.V7Tag73TranscriptSchedule

/-!
# Deterministic refinement of the deployed Tag-73 hash trace

This file refines a fixed Tag-73 tape against a fixed finite SHA-256 table.
It is deliberately below the probabilistic extraction game: there is no
witness, extractor, success bound, or knowledge-soundness conclusion here.

The important distinction is represented literally in the raw trace.  One
duplex squeeze performs two independent table lookups, first at
`state || 0x01` for the returned block and then at `state || 0x02` for the
next transcript state.  Grinding performs a lookup at
`state || 0x03 || nonce` without changing that state.  Query candidates are
run from clones of one post-final-nonce digest; discarded branches contribute
ordered oracle calls but never become the continuing transcript.

The finite table makes execution partial: a missing lookup or a selected work
nonce whose recorded digest misses its stage-local threshold stops refinement.
Sampler decoding is kept as an explicit deterministic interface and checked
by `checkedRefine`; it is not hidden in a conclusion-shaped premise.  In
particular, this module does not yet prove a Rust/source refinement theorem.
For a `.circlePoint` event, the imported schedule's 16-byte
`Messages.challengeValue` is treated only as the accepted QM31 parameter `t`;
the deployed Rust return is a 32-byte `(x,y)` secure circle point and is linked
by a separate decoder obligation below.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73DeterministicRefinement

open AspisK1.V7Tag73TranscriptSchedule

/-! ## A fixed finite lazy-oracle table -/

structure TableEntry where
  input : ByteString
  output : Digest256

abbrev FixedOracleTable := List TableEntry

/-- Ordered first-hit lookup in a fixed finite table.  Missing inputs make the
deterministic execution partial rather than receiving a fabricated default. -/
def tableLookup (table : FixedOracleTable) (input : ByteString) : Option Digest256 :=
  (table.find? fun entry => entry.input = input).map TableEntry.output

def TableWellFormed (table : FixedOracleTable) : Prop :=
  (table.map TableEntry.input).Nodup

theorem table_lookup_is_deterministic (table : FixedOracleTable)
    (input : ByteString) (first second : Digest256)
    (hfirst : tableLookup table input = some first)
    (hsecond : tableLookup table input = some second) :
    first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

/-! ## Raw query grammar and ordered trace -/

inductive SqueezeOwner where
  | challenge (id : ChallengeId)
  | queryCandidate (counter : Fin 64)
  deriving DecidableEq, Repr

inductive RawQueryRole where
  | absorb (payload : Payload)
  | squeezeOutput (owner : SqueezeOwner) (block : Nat)
  | squeezeAdvance (owner : SqueezeOwner) (block : Nat)
  | grind (stage : WorkStage) (nonce : NonceBytes)
  | publicRootSalt (context : Context) (treeTag : UInt8)

/-- Transcript-domain metadata when the query really has the deployed
`state || domain` grammar.  Public-root-salt hashing has its own literal ASCII
grammar and therefore deliberately returns `none`; no fictitious domain byte
is assigned to it. -/
def RawQueryRole.transcriptDomain? : RawQueryRole → Option UInt8
  | .absorb _ => some domAbsorb
  | .squeezeOutput _ _ => some domSqueeze
  | .squeezeAdvance _ _ => some domAdvance
  | .grind _ _ => some domGrind
  | .publicRootSalt _ _ => none

def RawQueryRole.input (before : Digest256) : RawQueryRole → ByteString
  | .absorb payload =>
      bytes before ++ [domAbsorb, payload.label] ++ payload.data
  | .squeezeOutput _ _ => bytes before ++ [domSqueeze]
  | .squeezeAdvance _ _ => bytes before ++ [domAdvance]
  | .grind _ nonce => bytes before ++ [domGrind] ++ bytes nonce
  | .publicRootSalt context treeTag => rootSaltInput context treeTag

def RawQueryRole.nextDigest (before output : Digest256) : RawQueryRole → Digest256
  | .absorb _ => output
  | .squeezeOutput _ _ => before
  | .squeezeAdvance _ _ => output
  | .grind _ _ => before
  | .publicRootSalt _ _ => before

/-- A raw call stores the state seen by that call and its one 256-bit answer.
Its input and successor state are derived, so malformed query grammars cannot
be represented by this type. -/
structure RawCall where
  role : RawQueryRole
  before : Digest256
  output : Digest256

def RawCall.input (call : RawCall) : ByteString :=
  call.role.input call.before

def RawCall.after (call : RawCall) : Digest256 :=
  call.role.nextDigest call.before call.output

theorem four_transcript_domains_are_pairwise_distinct :
    domAbsorb ≠ domSqueeze ∧
    domAbsorb ≠ domAdvance ∧
    domAbsorb ≠ domGrind ∧
    domSqueeze ≠ domAdvance ∧
    domSqueeze ≠ domGrind ∧
    domAdvance ≠ domGrind := by
  decide

theorem absorb_query_grammar (before output : Digest256) (payload : Payload) :
    (RawCall.mk (.absorb payload) before output).input =
      bytes before ++ [0, payload.label] ++ payload.data := by
  rfl

theorem squeeze_output_query_grammar (before output : Digest256)
    (owner : SqueezeOwner) (block : Nat) :
    (RawCall.mk (.squeezeOutput owner block) before output).input =
      bytes before ++ [1] := by
  rfl

theorem squeeze_advance_query_grammar (before output : Digest256)
    (owner : SqueezeOwner) (block : Nat) :
    (RawCall.mk (.squeezeAdvance owner block) before output).input =
      bytes before ++ [2] := by
  rfl

theorem squeeze_output_and_advance_inputs_are_distinct (before : Digest256) :
    bytes before ++ [domSqueeze] ≠ bytes before ++ [domAdvance] := by
  simp [domSqueeze, domAdvance]

theorem grind_query_grammar (before output : Digest256)
    (stage : WorkStage) (nonce : NonceBytes) :
    (RawCall.mk (.grind stage nonce) before output).input =
      bytes before ++ [3] ++ bytes nonce := by
  rfl

theorem public_root_salt_query_has_literal_grammar
    (before output : Digest256) (context : Context) (treeTag : UInt8) :
    (RawCall.mk (.publicRootSalt context treeTag) before output).input =
      publicRootSaltDomain ++ profileBinding ++ bytes context.programId ++
      bytes context.releaseBinding ++ bytes context.statementDigest ++
      bytes context.attemptId ++ [treeTag] := by
  rfl

theorem public_root_salt_has_no_transcript_domain_metadata
    (context : Context) (treeTag : UInt8) :
    (RawQueryRole.publicRootSalt context treeTag).transcriptDomain? = none := by
  rfl

theorem public_root_salt_query_length
    (before output : Digest256) (context : Context) (treeTag : UInt8) :
    (RawCall.mk (.publicRootSalt context treeTag) before output).input.length = 189 := by
  exact root_salt_input_length context treeTag

/-- The deployed grinding hash input does not contain a stage byte.  Stage
separation comes from the stage-local state, threshold, and later nonce absorb
label; the model does not invent a stronger grammar. -/
theorem grind_input_does_not_encode_stage (before : Digest256)
    (nonce : NonceBytes) (first second : WorkStage) :
    (RawQueryRole.grind first nonce).input before =
      (RawQueryRole.grind second nonce).input before := by
  rfl

structure SampleRecord where
  id : ChallengeId
  blocks : List Digest256

structure CandidateRecord where
  counter : Fin 64
  outcome : CandidateOutcome
  baseDigest : Digest256
  endDigest : Digest256
  blocks : List Digest256

structure EvalState where
  digest : Digest256
  calls : List RawCall
  samples : List SampleRecord
  candidates : List CandidateRecord

def initialEvalState : EvalState where
  digest := zeroBytes 32
  calls := []
  samples := []
  candidates := []

def queryStep (table : FixedOracleTable) (state : EvalState)
    (role : RawQueryRole) : Option (Digest256 × EvalState) :=
  let input := role.input state.digest
  match tableLookup table input with
  | none => none
  | some output =>
      let call := RawCall.mk role state.digest output
      some (output,
        { state with
          digest := call.after
          calls := state.calls ++ [call] })

theorem query_step_appends_one (table : FixedOracleTable) (state next : EvalState)
    (role : RawQueryRole) (output : Digest256)
    (run : queryStep table state role = some (output, next)) :
    tableLookup table (role.input state.digest) = some output ∧
    next.calls = state.calls ++ [RawCall.mk role state.digest output] ∧
    next.digest = role.nextDigest state.digest output := by
  simp only [queryStep] at run
  cases hlookup : tableLookup table (role.input state.digest) with
  | none => simp [hlookup] at run
  | some actual =>
      rw [hlookup] at run
      have pairEquals := Option.some.inj run
      cases pairEquals
      exact ⟨rfl, rfl, rfl⟩

def absorbStep (table : FixedOracleTable) (state : EvalState)
    (payload : Payload) : Option EvalState := do
  let (_, next) ← queryStep table state (.absorb payload)
  pure next

def rootSaltStep (table : FixedOracleTable) (state : EvalState)
    (context : Context) (treeTag : UInt8) : Option (Digest256 × EvalState) :=
  queryStep table state (.publicRootSalt context treeTag)

/-! ## Exact two-query squeeze and bounded block consumption -/

/-- Exactly two distinct table queries implement one duplex block.  The first
returns the raw block and keeps the digest fixed; the second independently
looks up `state || 0x02` and installs that answer as the next state. -/
def squeezeStep (table : FixedOracleTable) (state : EvalState)
    (owner : SqueezeOwner) (block : Nat) : Option (Digest256 × EvalState) := do
  let (output, afterOutput) ←
    queryStep table state (.squeezeOutput owner block)
  let (_, afterAdvance) ←
    queryStep table afterOutput (.squeezeAdvance owner block)
  pure (output, afterAdvance)

theorem squeeze_step_emits_two_distinct_queries
    (table : FixedOracleTable) (state next : EvalState)
    (owner : SqueezeOwner) (block : Nat) (output : Digest256)
    (run : squeezeStep table state owner block = some (output, next)) :
    tableLookup table (bytes state.digest ++ [1]) = some output ∧
    tableLookup table (bytes state.digest ++ [2]) = some next.digest ∧
    next.calls = state.calls ++
      [RawCall.mk (.squeezeOutput owner block) state.digest output,
       RawCall.mk (.squeezeAdvance owner block) state.digest next.digest] := by
  rw [squeezeStep] at run
  obtain ⟨outputPair, houtputStep, run⟩ := Option.bind_eq_some_iff.mp run
  rcases outputPair with ⟨blockOutput, afterOutput⟩
  dsimp only at run
  obtain ⟨advancePair, hadvanceStep, hresult⟩ :=
    Option.bind_eq_some_iff.mp run
  rcases advancePair with ⟨advanceOutput, afterAdvance⟩
  dsimp only at hresult
  have resultEquals := Option.some.inj hresult
  have outputEquals := congrArg Prod.fst resultEquals
  have nextEquals := congrArg Prod.snd resultEquals
  dsimp at outputEquals nextEquals
  subst output
  subst next
  obtain ⟨houtputLookup, houtputCalls, houtputDigest⟩ :=
    query_step_appends_one table state afterOutput
      (.squeezeOutput owner block) blockOutput houtputStep
  obtain ⟨hadvanceLookup, hadvanceCalls, hadvanceDigest⟩ :=
    query_step_appends_one table afterOutput afterAdvance
      (.squeezeAdvance owner block) advanceOutput hadvanceStep
  have houtputDigest' : afterOutput.digest = state.digest := by
    simpa only [RawQueryRole.nextDigest] using houtputDigest
  have hadvanceDigest' : afterAdvance.digest = advanceOutput := by
    simpa only [RawQueryRole.nextDigest] using hadvanceDigest
  constructor
  · simpa only [RawQueryRole.input, domSqueeze] using houtputLookup
  constructor
  · simpa only [RawQueryRole.input, domAdvance, houtputDigest', hadvanceDigest']
      using hadvanceLookup
  · calc
      afterAdvance.calls = afterOutput.calls ++
          [RawCall.mk (.squeezeAdvance owner block) afterOutput.digest advanceOutput] :=
        hadvanceCalls
      _ = state.calls ++
          [RawCall.mk (.squeezeOutput owner block) state.digest blockOutput,
           RawCall.mk (.squeezeAdvance owner block) state.digest afterAdvance.digest] := by
        rw [houtputCalls, houtputDigest', hadvanceDigest']
        simp

def squeezeManyFrom (table : FixedOracleTable) (owner : SqueezeOwner) :
    Nat → Nat → EvalState → Option (List Digest256 × EvalState)
  | _, 0, state => some ([], state)
  | firstBlock, count + 1, state => do
      let (output, next) ← squeezeStep table state owner firstBlock
      let (outputs, finalState) ←
        squeezeManyFrom table owner (firstBlock + 1) count next
      pure (output :: outputs, finalState)

def squeezeMany (table : FixedOracleTable) (owner : SqueezeOwner)
    (count : Nat) (state : EvalState) : Option (List Digest256 × EvalState) :=
  squeezeManyFrom table owner 0 count state

theorem squeeze_many_from_exact_sizes
    (table : FixedOracleTable) (owner : SqueezeOwner)
    (first count : Nat) (state finalState : EvalState)
    (outputs : List Digest256)
    (run : squeezeManyFrom table owner first count state = some (outputs, finalState)) :
    outputs.length = count ∧
    finalState.calls.length = state.calls.length + 2 * count := by
  induction count generalizing first state outputs finalState with
  | zero =>
      rw [squeezeManyFrom] at run
      cases Option.some.inj run
      simp
  | succ count ih =>
      rw [squeezeManyFrom] at run
      obtain ⟨firstPair, hblock, run⟩ := Option.bind_eq_some_iff.mp run
      rcases firstPair with ⟨output, blockState⟩
      obtain ⟨remainingPair, hremaining, hresult⟩ :=
        Option.bind_eq_some_iff.mp run
      rcases remainingPair with ⟨remainingOutputs, remainingState⟩
      cases Option.some.inj hresult
      have htwo := squeeze_step_emits_two_distinct_queries
        table state blockState owner first output hblock
      have hrest := ih (first := first + 1) (state := blockState)
        (outputs := remainingOutputs) (finalState := finalState) hremaining
      constructor
      · simp [hrest.1]
      · rw [hrest.2, htwo.2.2]
        simp
        omega

theorem squeeze_many_exact_sizes
    (table : FixedOracleTable) (owner : SqueezeOwner)
    (count : Nat) (state finalState : EvalState)
    (outputs : List Digest256)
    (run : squeezeMany table owner count state = some (outputs, finalState)) :
    outputs.length = count ∧
    finalState.calls.length = state.calls.length + 2 * count := by
  exact squeeze_many_from_exact_sizes table owner 0 count state finalState outputs run

/-! ## Exact stage-local grinding -/

def firstEightBytes (digest : Digest256) : List UInt8 :=
  List.ofFn fun index : Fin 8 =>
    digest ⟨index.val, Nat.lt_trans index.isLt (by decide : 8 < 32)⟩

def bigEndianHead64 (digest : Digest256) : Nat :=
  (firstEightBytes digest).foldl (fun value byte => value * 256 + byte.toNat) 0

def workDigestAccepted (stage : WorkStage) (digest : Digest256) : Bool :=
  decide (bigEndianHead64 digest < 2 ^ (64 - workBits stage))

theorem work_digest_accepted_iff (stage : WorkStage) (digest : Digest256) :
    workDigestAccepted stage digest = true ↔
      bigEndianHead64 digest < 2 ^ (64 - workBits stage) := by
  simp [workDigestAccepted]

def grindProbe (table : FixedOracleTable) (state : EvalState)
    (stage : WorkStage) (nonce : NonceBytes) :
    Option (Digest256 × EvalState) :=
  queryStep table state (.grind stage nonce)

theorem grind_probe_does_not_advance
    (table : FixedOracleTable) (state next : EvalState)
    (stage : WorkStage) (nonce : NonceBytes) (output : Digest256)
    (run : grindProbe table state stage nonce = some (output, next)) :
    next.digest = state.digest := by
  have step := query_step_appends_one table state next (.grind stage nonce) output run
  exact step.2.2

/-- These probes represent adversary oracle-history data.  They are neither
serialized in the proof nor replayed by the deployed verifier.  The verifier
itself performs exactly the final `selected` probe. -/
def runGrindingProbes (table : FixedOracleTable) (stage : WorkStage) :
    List NonceBytes → EvalState → Option EvalState
  | [], state => some state
  | nonce :: rest, state => do
      let (_, next) ← grindProbe table state stage nonce
      runGrindingProbes table stage rest next

theorem grinding_probes_do_not_advance
    (table : FixedOracleTable) (stage : WorkStage)
    (probes : List NonceBytes) (state next : EvalState)
    (run : runGrindingProbes table stage probes state = some next) :
    next.digest = state.digest := by
  induction probes generalizing state with
  | nil =>
      rw [runGrindingProbes] at run
      exact (congrArg EvalState.digest (Option.some.inj run)).symm
  | cons nonce rest ih =>
      rw [runGrindingProbes] at run
      obtain ⟨probePair, hprobe, hrest⟩ := Option.bind_eq_some_iff.mp run
      rcases probePair with ⟨output, probeState⟩
      dsimp only at hrest
      exact (ih (state := probeState) hrest).trans
        (grind_probe_does_not_advance table state probeState stage nonce output hprobe)

def runGrindingChoice (table : FixedOracleTable) (state : EvalState)
    (stage : WorkStage) (choice : GrindingChoice stage) : Option EvalState := do
  let queried ← runGrindingProbes table stage choice.probesBeforeSelected state
  let (digest, afterSelected) ← grindProbe table queried stage choice.selected
  if workDigestAccepted stage digest then
    pure afterSelected
  else
    none

/-- Work-erased replay performs exactly the same adversary-history probes and
the verifier-visible selected-nonce probe, but omits only the stage-local
leading-zero rejection.  In particular, it does not erase a nonce, an absorb,
or an oracle call. -/
def runGrindingChoiceWorkErased (table : FixedOracleTable) (state : EvalState)
    (stage : WorkStage) (choice : GrindingChoice stage) : Option EvalState := do
  let queried ← runGrindingProbes table stage choice.probesBeforeSelected state
  let (_, afterSelected) ← grindProbe table queried stage choice.selected
  pure afterSelected

theorem grinding_choice_success_survives_work_erasure
    (table : FixedOracleTable) (state next : EvalState)
    (stage : WorkStage) (choice : GrindingChoice stage)
    (run : runGrindingChoice table state stage choice = some next) :
    runGrindingChoiceWorkErased table state stage choice = some next := by
  rw [runGrindingChoice] at run
  obtain ⟨queried, hprobes, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨selectedPair, hselected, run⟩ := Option.bind_eq_some_iff.mp run
  rcases selectedPair with ⟨digest, afterSelected⟩
  dsimp only at run
  by_cases hwork : workDigestAccepted stage digest = true
  · simp only [hwork, if_true] at run
    have afterEqualsNext : afterSelected = next := by
      simpa only [pure, Option.some.injEq] using run
    rw [runGrindingChoiceWorkErased]
    apply Option.bind_eq_some_iff.mpr
    refine ⟨queried, hprobes, ?_⟩
    apply Option.bind_eq_some_iff.mpr
    exact ⟨(digest, afterSelected), hselected,
      by simpa only [pure, Option.some.injEq] using afterEqualsNext⟩
  · simp [hwork] at run

theorem grinding_choice_does_not_advance
    (table : FixedOracleTable) (state next : EvalState)
    (stage : WorkStage) (choice : GrindingChoice stage)
    (run : runGrindingChoice table state stage choice = some next) :
    next.digest = state.digest := by
  rw [runGrindingChoice] at run
  obtain ⟨queried, hprobes, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨selectedPair, hselected, run⟩ := Option.bind_eq_some_iff.mp run
  rcases selectedPair with ⟨digest, afterSelected⟩
  dsimp only at run
  by_cases hwork : workDigestAccepted stage digest = true
  · simp only [hwork, if_true] at run
    have afterEqualsNext : afterSelected = next := by
      simpa only [pure, Option.some.injEq] using run
    subst next
    exact (grind_probe_does_not_advance table queried afterSelected stage
      choice.selected digest hselected).trans
        (grinding_probes_do_not_advance table stage
          choice.probesBeforeSelected state queried hprobes)
  · simp [hwork] at run

def noncePayload : (stage : WorkStage) → NonceBytes → Payload
  | .batch, nonce => .batchNonce nonce
  | .fold, nonce => .foldNonce nonce
  | .final, nonce => .finalNonce nonce

theorem stage_nonce_absorb_labels_are_distinct (nonce : NonceBytes) :
    (noncePayload .batch nonce).label = 28 ∧
    (noncePayload .fold nonce).label = 20 ∧
    (noncePayload .final nonce).label = 5 := by
  exact ⟨rfl, rfl, rfl⟩

theorem stage_local_work_thresholds :
    workBits .batch = 35 ∧ workBits .fold = 31 ∧ workBits .final = 34 :=
  three_work_stages_are_distinct

/-! ## Linear machine events -/

def runMachineEvent (table : FixedOracleTable) (state : EvalState) :
    MachineEvent → Option EvalState
  | .absorb payload => absorbStep table state payload
  | .challenge id use => do
      let (blocks, next) ← squeezeMany table (.challenge id) use.blocksUsed state
      pure { next with samples := next.samples ++ [{ id, blocks }] }
  | .grind stage choice => runGrindingChoice table state stage choice
  | .check _ => some state

def runMachineEvents (table : FixedOracleTable) :
    List MachineEvent → EvalState → Option EvalState
  | [], state => some state
  | event :: rest, state => do
      let next ← runMachineEvent table state event
      runMachineEvents table rest next

/-- Event replay with only the three leading-zero gates erased. -/
def runMachineEventWorkErased (table : FixedOracleTable) (state : EvalState) :
    MachineEvent → Option EvalState
  | .absorb payload => absorbStep table state payload
  | .challenge id use => do
      let (blocks, next) ← squeezeMany table (.challenge id) use.blocksUsed state
      pure { next with samples := next.samples ++ [{ id, blocks }] }
  | .grind stage choice => runGrindingChoiceWorkErased table state stage choice
  | .check _ => some state

def runMachineEventsWorkErased (table : FixedOracleTable) :
    List MachineEvent → EvalState → Option EvalState
  | [], state => some state
  | event :: rest, state => do
      let next ← runMachineEventWorkErased table state event
      runMachineEventsWorkErased table rest next

theorem machine_event_success_survives_work_erasure
    (table : FixedOracleTable) (state next : EvalState) (event : MachineEvent)
    (run : runMachineEvent table state event = some next) :
    runMachineEventWorkErased table state event = some next := by
  cases event with
  | absorb payload => simpa [runMachineEvent, runMachineEventWorkErased] using run
  | challenge id use => simpa [runMachineEvent, runMachineEventWorkErased] using run
  | grind stage choice =>
      exact grinding_choice_success_survives_work_erasure table state next stage choice run
  | check check => simpa [runMachineEvent, runMachineEventWorkErased] using run

theorem machine_events_success_survives_work_erasure
    (table : FixedOracleTable) (events : List MachineEvent)
    (state next : EvalState)
    (run : runMachineEvents table events state = some next) :
    runMachineEventsWorkErased table events state = some next := by
  induction events generalizing state with
  | nil => simpa [runMachineEvents, runMachineEventsWorkErased] using run
  | cons event rest ih =>
      rw [runMachineEvents] at run
      obtain ⟨eventState, hevent, hrest⟩ := Option.bind_eq_some_iff.mp run
      have erasedEvent := machine_event_success_survives_work_erasure
        table state eventState event hevent
      have erasedRest := ih (state := eventState) hrest
      rw [runMachineEventsWorkErased]
      exact Option.bind_eq_some_iff.mpr ⟨eventState, erasedEvent, erasedRest⟩

/-! ## Exact prefix with root-salt calls in their Rust order -/

def prefixBeforeC1 (messages : Messages) : List MachineEvent :=
  let context := messages.context
  [.check .canonicalWire,
   .absorb .profile,
   .absorb .circleBasis,
   .absorb (.deployment context),
   .absorb (.statement context.statementDigest),
   .absorb (.hidingPrecommit context)]

def prefixAfterC2 (messages : Messages) : List MachineEvent :=
  [.absorb .constraintRegistry,
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

def runPrefix (table : FixedOracleTable) (messages : Messages) : Option EvalState := do
  let beforeC1 ← runMachineEvents table (prefixBeforeC1 messages) initialEvalState
  let (c1Salt, withC1SaltQuery) ←
    rootSaltStep table beforeC1 messages.context c1TreeTag
  let afterC1 ← absorbStep table withC1SaltQuery (.c1Root messages.c1Root c1Salt)
  let afterPhaseChallenges ← runMachineEvents table
    [challengeEvent messages .lambda, challengeEvent messages .chi] afterC1
  let (c2Salt, withC2SaltQuery) ←
    rootSaltStep table afterPhaseChallenges messages.context c2TreeTag
  let afterC2 ← absorbStep table withC2SaltQuery (.c2Root messages.c2.root c2Salt)
  runMachineEvents table (prefixAfterC2 messages) afterC2

def runPrefixWorkErased (table : FixedOracleTable)
    (messages : Messages) : Option EvalState := do
  let beforeC1 ←
    runMachineEventsWorkErased table (prefixBeforeC1 messages) initialEvalState
  let (c1Salt, withC1SaltQuery) ←
    rootSaltStep table beforeC1 messages.context c1TreeTag
  let afterC1 ← absorbStep table withC1SaltQuery (.c1Root messages.c1Root c1Salt)
  let afterPhaseChallenges ← runMachineEventsWorkErased table
    [challengeEvent messages .lambda, challengeEvent messages .chi] afterC1
  let (c2Salt, withC2SaltQuery) ←
    rootSaltStep table afterPhaseChallenges messages.context c2TreeTag
  let afterC2 ← absorbStep table withC2SaltQuery (.c2Root messages.c2.root c2Salt)
  runMachineEventsWorkErased table (prefixAfterC2 messages) afterC2

theorem prefix_success_survives_work_erasure
    (table : FixedOracleTable) (messages : Messages) (next : EvalState)
    (run : runPrefix table messages = some next) :
    runPrefixWorkErased table messages = some next := by
  rw [runPrefix] at run
  obtain ⟨beforeC1, hbeforeC1, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨c1Pair, hc1Salt, run⟩ := Option.bind_eq_some_iff.mp run
  rcases c1Pair with ⟨c1Salt, withC1SaltQuery⟩
  obtain ⟨afterC1, hafterC1, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨afterPhaseChallenges, hphase, run⟩ :=
    Option.bind_eq_some_iff.mp run
  obtain ⟨c2Pair, hc2Salt, run⟩ := Option.bind_eq_some_iff.mp run
  rcases c2Pair with ⟨c2Salt, withC2SaltQuery⟩
  obtain ⟨afterC2, hafterC2, hrest⟩ := Option.bind_eq_some_iff.mp run
  rw [runPrefixWorkErased]
  apply Option.bind_eq_some_iff.mpr
  refine ⟨beforeC1,
    machine_events_success_survives_work_erasure table _ _ _ hbeforeC1, ?_⟩
  apply Option.bind_eq_some_iff.mpr
  refine ⟨(c1Salt, withC1SaltQuery), hc1Salt, ?_⟩
  apply Option.bind_eq_some_iff.mpr
  refine ⟨afterC1, hafterC1, ?_⟩
  apply Option.bind_eq_some_iff.mpr
  refine ⟨afterPhaseChallenges,
    machine_events_success_survives_work_erasure table _ _ _ hphase, ?_⟩
  apply Option.bind_eq_some_iff.mpr
  refine ⟨(c2Salt, withC2SaltQuery), hc2Salt, ?_⟩
  apply Option.bind_eq_some_iff.mpr
  exact ⟨afterC2, hafterC2,
    machine_events_success_survives_work_erasure table _ _ _ hrest⟩

/-! ## Cloned first-cap-203 candidate branches -/

structure CandidateSpec where
  counter : Fin 64
  outcome : CandidateOutcome

structure Q16Tape where
  earlier : List CandidateSpec
  selected : CandidateSpec

def earlierSpecs {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) : List CandidateSpec :=
  (List.finRange search.selectedCounter.val).map fun counter =>
    let lifted : Fin 64 :=
      ⟨counter.val, Nat.lt_trans counter.isLt search.selectedCounter.isLt⟩
    { counter := lifted, outcome := search.outcome lifted }

def q16TapeOfSearch {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) : Q16Tape where
  earlier := earlierSpecs search
  selected :=
    { counter := search.selectedCounter
      outcome := .schedule search.selectedSchedule }

def runCandidate (table : FixedOracleTable) (state : EvalState)
    (spec : CandidateSpec) : Option EvalState := do
  let base := state.digest
  let afterCounter ← absorbStep table state (.queryCandidate spec.counter)
  let (blocks, afterBlocks) ← squeezeMany table (.queryCandidate spec.counter)
    spec.outcome.blocksUsed afterCounter
  pure
    { afterBlocks with
      candidates := afterBlocks.candidates ++
        [{ counter := spec.counter
           outcome := spec.outcome
           baseDigest := base
           endDigest := afterBlocks.digest
           blocks }] }

def restoreDigest (digest : Digest256) (state : EvalState) : EvalState :=
  { state with digest }

def runDiscardedCandidates (table : FixedOracleTable) (base : Digest256) :
    List CandidateSpec → EvalState → Option EvalState
  | [], state => some state
  | spec :: rest, state => do
      let branch ← runCandidate table state spec
      runDiscardedCandidates table base rest (restoreDigest base branch)

theorem discarded_candidates_restore_one_base
    (table : FixedOracleTable) (base : Digest256)
    (specs : List CandidateSpec) (state next : EvalState)
    (atBase : state.digest = base)
    (run : runDiscardedCandidates table base specs state = some next) :
    next.digest = base := by
  induction specs generalizing state with
  | nil =>
      rw [runDiscardedCandidates] at run
      have stateEqualsNext := Option.some.inj run
      exact (congrArg EvalState.digest stateEqualsNext).symm.trans atBase
  | cons spec rest ih =>
      rw [runDiscardedCandidates] at run
      obtain ⟨branch, hbranch, hrest⟩ := Option.bind_eq_some_iff.mp run
      exact ih (state := restoreDigest base branch) rfl hrest

def runQ16 (table : FixedOracleTable) (baseState : EvalState)
    (tape : Q16Tape) : Option EvalState := do
  let beforeSelected ←
    runDiscardedCandidates table baseState.digest tape.earlier baseState
  runCandidate table beforeSelected tape.selected

theorem selected_q16_branch_starts_from_shared_base
    (table : FixedOracleTable) (baseState beforeSelected finalState : EvalState)
    (tape : Q16Tape)
    (earlierRun : runDiscardedCandidates table baseState.digest tape.earlier baseState =
      some beforeSelected)
    (selectedRun : runCandidate table beforeSelected tape.selected = some finalState) :
    beforeSelected.digest = baseState.digest ∧
    runQ16 table baseState tape = some finalState := by
  constructor
  · exact discarded_candidates_restore_one_base table baseState.digest tape.earlier
      baseState beforeSelected rfl earlierRun
  · simp [runQ16, earlierRun, selectedRun]

/-! ## Actual deterministic partial refinement -/

structure SecureCirclePointBytes where
  x : Qm31Bytes
  y : Qm31Bytes

structure DeployedFixedTape where
  frontierNodes : QuerySchedule → Nat
  messages : Messages
  search : FirstCap203Search frontierNodes
  /-- The actual 32-byte Rust return from each secure-circle sample.  The
  corresponding `messages.challengeValue (.circlePoint sample)` is only its
  accepted 16-byte parameter. -/
  circlePoints : Fin 2 → SecureCirclePointBytes

structure InteractiveRawTrace where
  initialDigest : Digest256
  q16BaseDigest : Digest256
  selectedCounter : Fin 64
  finalDigest : Digest256
  circlePoints : Fin 2 → SecureCirclePointBytes
  calls : List RawCall
  samples : List SampleRecord
  candidates : List CandidateRecord

/-- Deterministically replay the deployed fixed tape against the fixed table.
No witness or extraction conclusion occurs in this map. -/
def refine (table : FixedOracleTable) (tape : DeployedFixedTape) :
    Option InteractiveRawTrace := do
  let prefixState ← runPrefix table tape.messages
  let q16Base := prefixState.digest
  let afterQ16 ← runQ16 table prefixState (q16TapeOfSearch tape.search)
  let finalState ←
    runMachineEvents table (afterAcceptedQueryScan tape.messages) afterQ16
  pure
    { initialDigest := initialEvalState.digest
      q16BaseDigest := q16Base
      selectedCounter := tape.search.selectedCounter
      finalDigest := finalState.digest
      circlePoints := tape.circlePoints
      calls := finalState.calls
      samples := finalState.samples
      candidates := finalState.candidates }

/-- The same fixed-table replay with only the three stage-local work predicates
erased.  All three selected nonces, their grind queries, their subsequent
absorbs, and all adversary-history probes remain in the ordered trace. -/
def refineWorkErased (table : FixedOracleTable) (tape : DeployedFixedTape) :
    Option InteractiveRawTrace := do
  let prefixState ← runPrefixWorkErased table tape.messages
  let q16Base := prefixState.digest
  let afterQ16 ← runQ16 table prefixState (q16TapeOfSearch tape.search)
  let finalState ←
    runMachineEventsWorkErased table (afterAcceptedQueryScan tape.messages) afterQ16
  pure
    { initialDigest := initialEvalState.digest
      q16BaseDigest := q16Base
      selectedCounter := tape.search.selectedCounter
      finalDigest := finalState.digest
      circlePoints := tape.circlePoints
      calls := finalState.calls
      samples := finalState.samples
      candidates := finalState.candidates }

theorem refinement_success_survives_work_erasure
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (raw : InteractiveRawTrace)
    (run : refine table tape = some raw) :
    refineWorkErased table tape = some raw := by
  rw [refine] at run
  obtain ⟨prefixState, hprefix, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨afterQ16, hq16, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨finalState, hfinal, hraw⟩ := Option.bind_eq_some_iff.mp run
  have rawEquation := Option.some.inj hraw
  rw [← rawEquation]
  rw [refineWorkErased]
  apply Option.bind_eq_some_iff.mpr
  refine ⟨prefixState,
    prefix_success_survives_work_erasure table tape.messages prefixState hprefix, ?_⟩
  apply Option.bind_eq_some_iff.mpr
  refine ⟨afterQ16, hq16, ?_⟩
  apply Option.bind_eq_some_iff.mpr
  exact ⟨finalState,
    machine_events_success_survives_work_erasure table _ _ _ hfinal, rfl⟩

structure DeterministicDecoders where
  /-- For `.circlePoint`, this returns the accepted bounded-sampler parameter
  `t`, not the Rust `SecureCirclePoint` return. -/
  qm31Parameter : (id : ChallengeId) →
    List Digest256 → Option Qm31Bytes
  /-- Exact rational map plus its deployed admissibility checks, represented
  separately because the Rust return contains two QM31 coordinates. -/
  secureCirclePoint : Qm31Bytes → Option SecureCirclePointBytes
  candidate : Fin 64 → List Digest256 → Option CandidateOutcome

/-! This layer keeps the decoder record abstract so its fixed-table proofs do
not import the exact field tower.  `V7Tag73SamplerDecoder` and
`V7Tag73SecureCircleMap` provide the concrete deployed instantiation. -/

def expectedCandidateSpecs (tape : DeployedFixedTape) : List CandidateSpec :=
  let q16 := q16TapeOfSearch tape.search
  q16.earlier ++ [q16.selected]

/-- Explicit non-circular trace well-formedness.  These fields concern only
the fixed table, deterministic sampler decoders, and the raw observations.
They do not state acceptance, extraction, or a security conclusion. -/
structure TraceWellFormed (table : FixedOracleTable)
    (decoders : DeterministicDecoders) (tape : DeployedFixedTape)
    (raw : InteractiveRawTrace) : Prop where
  tableFunctional : TableWellFormed table
  challengesDecode : ∀ record ∈ raw.samples,
    decoders.qm31Parameter record.id record.blocks =
      some (tape.messages.challengeValue record.id)
  secureCirclePointsDecode : ∀ sample,
    decoders.secureCirclePoint
        (tape.messages.challengeValue (.circlePoint sample)) =
      some (tape.circlePoints sample)
  candidatesDecode : ∀ record ∈ raw.candidates,
    decoders.candidate record.counter record.blocks = some record.outcome
  candidateProjection :
    raw.candidates.map (fun record => (record.counter, record.outcome)) =
      (expectedCandidateSpecs tape).map (fun spec => (spec.counter, spec.outcome))
  clonedCandidateBase : ∀ record ∈ raw.candidates,
    record.baseDigest = raw.q16BaseDigest

noncomputable def checkedRefine (table : FixedOracleTable)
    (decoders : DeterministicDecoders) (tape : DeployedFixedTape) :
    Option InteractiveRawTrace := by
  classical
  exact
    match refined : refine table tape with
    | none => none
    | some raw =>
        if TraceWellFormed table decoders tape raw then some raw else none

noncomputable def checkedRefineWorkErased (table : FixedOracleTable)
    (decoders : DeterministicDecoders) (tape : DeployedFixedTape) :
    Option InteractiveRawTrace := by
  classical
  exact
    match refined : refineWorkErased table tape with
    | none => none
    | some raw =>
        if TraceWellFormed table decoders tape raw then some raw else none

def IsDeterministicRefinement (table : FixedOracleTable)
    (decoders : DeterministicDecoders) (tape : DeployedFixedTape)
    (raw : InteractiveRawTrace) : Prop :=
  checkedRefine table decoders tape = some raw

theorem checked_refinement_is_well_formed
    (table : FixedOracleTable) (decoders : DeterministicDecoders)
    (tape : DeployedFixedTape) (raw : InteractiveRawTrace)
    (run : checkedRefine table decoders tape = some raw) :
    refine table tape = some raw ∧ TraceWellFormed table decoders tape raw := by
  classical
  unfold checkedRefine at run
  split at run <;> simp_all
  rcases run with ⟨hwf, hraw⟩
  subst raw
  exact hwf

theorem checked_refinement_success_survives_work_erasure
    (table : FixedOracleTable) (decoders : DeterministicDecoders)
    (tape : DeployedFixedTape) (raw : InteractiveRawTrace)
    (run : checkedRefine table decoders tape = some raw) :
    checkedRefineWorkErased table decoders tape = some raw := by
  classical
  obtain ⟨hrefine, hwf⟩ := checked_refinement_is_well_formed table decoders tape raw run
  have herased := refinement_success_survives_work_erasure table tape raw hrefine
  rw [checkedRefineWorkErased, herased]
  simp [hwf]

theorem checked_refinement_preserves_selected_counter
    (table : FixedOracleTable) (decoders : DeterministicDecoders)
    (tape : DeployedFixedTape) (raw : InteractiveRawTrace)
    (run : checkedRefine table decoders tape = some raw) :
    raw.selectedCounter = tape.search.selectedCounter := by
  obtain ⟨hrefine, _⟩ := checked_refinement_is_well_formed table decoders tape raw run
  rw [refine] at hrefine
  obtain ⟨prefixState, hprefix, hrefine⟩ := Option.bind_eq_some_iff.mp hrefine
  obtain ⟨afterQ16, hq16, hrefine⟩ := Option.bind_eq_some_iff.mp hrefine
  obtain ⟨finalState, hfinal, hraw⟩ := Option.bind_eq_some_iff.mp hrefine
  have rawEquation := Option.some.inj hraw
  exact (congrArg InteractiveRawTrace.selectedCounter rawEquation).symm

def RawAccepts (check : InteractiveRawTrace → Bool)
    (raw : InteractiveRawTrace) : Prop :=
  check raw = true

def RefinedModelAccepts (table : FixedOracleTable) (decoders : DeterministicDecoders)
    (check : InteractiveRawTrace → Bool) (tape : DeployedFixedTape) : Prop :=
  ∃ raw, checkedRefine table decoders tape = some raw ∧ check raw = true

def WorkErasedModelAccepts (table : FixedOracleTable)
    (decoders : DeterministicDecoders)
    (check : InteractiveRawTrace → Bool) (tape : DeployedFixedTape) : Prop :=
  ∃ raw, checkedRefineWorkErased table decoders tape = some raw ∧ check raw = true

/-- Acceptance preservation is a deterministic projection theorem: the same
external terminal predicate is applied to the actual refined raw trace.  It
does not assert that the predicate implies a witness. -/
theorem checked_refinement_preserves_acceptance
    (table : FixedOracleTable) (decoders : DeterministicDecoders)
    (check : InteractiveRawTrace → Bool) (tape : DeployedFixedTape)
    (raw : InteractiveRawTrace)
    (refinement : checkedRefine table decoders tape = some raw)
    (accepted : RefinedModelAccepts table decoders check tape) :
    RawAccepts check raw := by
  obtain ⟨other, hother, haccepted⟩ := accepted
  have : other = raw := by
    rw [refinement] at hother
    exact Option.some.inj hother.symm
  subst other
  exact haccepted

/-- Pointwise work-erasure monotonicity.  Exact modeled acceptance is a subset
of acceptance after dropping only the three leading-zero checks.  No division
by work, independence hypothesis, or probabilistic claim is involved. -/
theorem refined_model_accepts_implies_work_erased_model_accepts
    (table : FixedOracleTable) (decoders : DeterministicDecoders)
    (check : InteractiveRawTrace → Bool) (tape : DeployedFixedTape) :
    RefinedModelAccepts table decoders check tape →
      WorkErasedModelAccepts table decoders check tape := by
  rintro ⟨raw, hrefine, haccept⟩
  exact ⟨raw,
    checked_refinement_success_survives_work_erasure table decoders tape raw hrefine,
    haccept⟩

#print axioms table_lookup_is_deterministic
#print axioms four_transcript_domains_are_pairwise_distinct
#print axioms absorb_query_grammar
#print axioms squeeze_output_query_grammar
#print axioms squeeze_advance_query_grammar
#print axioms squeeze_output_and_advance_inputs_are_distinct
#print axioms grind_query_grammar
#print axioms public_root_salt_query_has_literal_grammar
#print axioms public_root_salt_has_no_transcript_domain_metadata
#print axioms public_root_salt_query_length
#print axioms grind_input_does_not_encode_stage
#print axioms query_step_appends_one
#print axioms squeeze_step_emits_two_distinct_queries
#print axioms squeeze_many_exact_sizes
#print axioms grind_probe_does_not_advance
#print axioms grinding_probes_do_not_advance
#print axioms grinding_choice_does_not_advance
#print axioms grinding_choice_success_survives_work_erasure
#print axioms machine_events_success_survives_work_erasure
#print axioms stage_nonce_absorb_labels_are_distinct
#print axioms stage_local_work_thresholds
#print axioms discarded_candidates_restore_one_base
#print axioms selected_q16_branch_starts_from_shared_base
#print axioms checked_refinement_is_well_formed
#print axioms checked_refinement_preserves_selected_counter
#print axioms checked_refinement_preserves_acceptance
#print axioms refinement_success_survives_work_erasure
#print axioms checked_refinement_success_survives_work_erasure
#print axioms refined_model_accepts_implies_work_erased_model_accepts

end AspisK1.V7Tag73DeterministicRefinement
