import AspisFormal.K1.V7Tag73FutureFreeCheckedRefinementBisimulation
import AspisFormal.K1.V7Tag73RawFutureFreeDriver

/-!
# Checked Tag-73 refinement as an operational future-free query path

This file connects the strict fixed-table refinement to the raw, future-free
verifier driver.  The bridge is deliberately operational: oracle answers are
justified by lookups in the same fixed table, the driver emits an actual
`MachineQueryPath`, and its terminal statement is schedule exhaustion rather
than semantic or Merkle acceptance.

The first section supplies reusable path-composition infrastructure.  The
protocol-specific construction below follows the checked refinement's actual
prefix, q16 forest and post-scan execution; it never receives a trace-cover,
restore function, acceptance predicate or extractor conclusion.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73CheckedRefinementFutureFreePath

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73RefinementExecutionBridge
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73ResumeDerivedReplayNode
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7FsAokExperiment

noncomputable section

/-! ## Fixed-table query paths -/

/-- Every pair on a machine path is an actual answer in one fixed oracle
table.  This is the condition that prevents `MachineQueryPath` from choosing
convenient, unrelated answers. -/
def PathUsesFixedTable (table : FixedOracleTable)
    (pairs : List (ShaInput × ShaOutput)) : Prop :=
  ∀ pair ∈ pairs, tableLookup table pair.1 = some pair.2

@[simp] theorem path_uses_fixed_table_nil (table : FixedOracleTable) :
    PathUsesFixedTable table [] := by
  simp [PathUsesFixedTable]

theorem path_uses_fixed_table_cons
    (table : FixedOracleTable) (input : ShaInput) (output : ShaOutput)
    (pairs : List (ShaInput × ShaOutput))
    (head : tableLookup table input = some output)
    (tail : PathUsesFixedTable table pairs) :
    PathUsesFixedTable table ((input, output) :: pairs) := by
  intro pair member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact head
  · exact tail pair member

theorem path_uses_fixed_table_append
    (table : FixedOracleTable) (first second : List (ShaInput × ShaOutput))
    (hfirst : PathUsesFixedTable table first)
    (hsecond : PathUsesFixedTable table second) :
    PathUsesFixedTable table (first ++ second) := by
  intro pair member
  rcases List.mem_append.mp member with member | member
  · exact hfirst pair member
  · exact hsecond pair member

theorem machine_query_path_bind_join
    {First Second : Type*} (program : OracleMachine First)
    (next : First → OracleMachine Second)
    (headPairs tailPairs : List (ShaInput × ShaOutput))
    (value : First) (result : Second)
    (head : MachineQueryPath program headPairs value)
    (tail : MachineQueryPath (next value) tailPairs result) :
    MachineQueryPath (bindOracleMachine program next)
      (headPairs ++ tailPairs) result := by
  induction head with
  | pure value => exact tail
  | query input continuation output pairs value head ih =>
      exact .query input _ output (pairs ++ tailPairs) result (ih tail)

theorem fixed_table_absorb_reply_path
    (table : FixedOracleTable) (state : FutureFreeVerifierState)
    (payload : Payload) (output : Digest256)
    (lookup : tableLookup table
      (bytes state.current.core.digest ++
        [domAbsorb, payload.label] ++ payload.data) = some output) :
    MachineQueryPath
      (futureFreeReplyProgram state (.absorb payload))
      [(bytes state.current.core.digest ++
          [domAbsorb, payload.label] ++ payload.data, output)]
      (VerifierReply.single output) := by
  change MachineQueryPath
    (.query (bytes state.current.core.digest ++
      [domAbsorb, payload.label] ++ payload.data) fun answer =>
        .pure (VerifierReply.single answer)) _ _
  exact .query _ _ output [] (VerifierReply.single output) (.pure _)

theorem fixed_table_work_reply_path
    (table : FixedOracleTable) (state : FutureFreeVerifierState)
    (stage : WorkStage) (nonce : NonceBytes) (kind : WorkProbeKind)
    (output : Digest256)
    (lookup : tableLookup table
      (bytes state.current.core.digest ++ [domGrind] ++ bytes nonce) =
        some output) :
    MachineQueryPath
      (futureFreeReplyProgram state (.workProbe stage nonce kind))
      [(bytes state.current.core.digest ++ [domGrind] ++ bytes nonce, output)]
      (VerifierReply.single output) := by
  change MachineQueryPath
    (.query (bytes state.current.core.digest ++ [domGrind] ++ bytes nonce)
      fun answer => .pure (VerifierReply.single answer)) _ _
  exact .query _ _ output [] (VerifierReply.single output) (.pure _)

theorem fixed_table_root_salt_reply_path
    (table : FixedOracleTable) (state : FutureFreeVerifierState)
    (tree : AuthenticatedTree) (output : Digest256)
    (lookup : tableLookup table
      (rootSaltInput state.current.bindings.context tree.tag) = some output) :
    MachineQueryPath
      (futureFreeReplyProgram state (.requestRootSalt tree))
      [(rootSaltInput state.current.bindings.context tree.tag, output)]
      (VerifierReply.single output) := by
  change MachineQueryPath
    (.query (rootSaltInput state.current.bindings.context tree.tag)
      fun answer => .pure (VerifierReply.single answer)) _ _
  exact .query _ _ output [] (VerifierReply.single output) (.pure _)

theorem fixed_table_absorb_c1_reply_path
    (table : FixedOracleTable) (state : FutureFreeVerifierState)
    (root : TypedMerkleRoot .initialC1) (salt output : Digest256)
    (saved : state.current.core.c1Salt = some salt)
    (lookup : tableLookup table
      (bytes state.current.core.digest ++
        [domAbsorb, c1RootLabel] ++
          (Payload.c1Root root.value salt).data) =
        some output) :
    MachineQueryPath
      (futureFreeReplyProgram state (.absorbC1 root))
      [(bytes state.current.core.digest ++
          [domAbsorb, c1RootLabel] ++
            (Payload.c1Root root.value salt).data, output)]
      (VerifierReply.single output) := by
  simp only [futureFreeReplyProgram, structuralFutureFreeReply, actionInputs,
    saved]
  exact .query _ _ output [] (VerifierReply.single output) (.pure _)

theorem fixed_table_absorb_c2_reply_path
    (table : FixedOracleTable) (state : FutureFreeVerifierState)
    (lambda chi : Qm31Bytes) (commitment : C2Commitment lambda chi)
    (salt output : Digest256)
    (saved : state.current.core.c2Salt = some salt)
    (lookup : tableLookup table
      (bytes state.current.core.digest ++
        [domAbsorb, c2RootLabel] ++
          (Payload.c2Root commitment.root salt).data) =
        some output) :
    MachineQueryPath
      (futureFreeReplyProgram state (.absorbC2 lambda chi commitment))
      [(bytes state.current.core.digest ++
          [domAbsorb, c2RootLabel] ++
            (Payload.c2Root commitment.root salt).data,
        output)]
      (VerifierReply.single output) := by
  simp only [futureFreeReplyProgram, structuralFutureFreeReply, actionInputs,
    saved]
  exact .query _ _ output [] (VerifierReply.single output) (.pure _)

theorem fixed_table_q16_absorb_reply_path
    (table : FixedOracleTable) (state : FutureFreeVerifierState)
    (counter : Fin 64) (output : Digest256)
    (lookup : tableLookup table
      (bytes state.current.core.digest ++
        [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val]) =
        some output) :
    MachineQueryPath
      (futureFreeReplyProgram state (.absorb (.queryCandidate counter)))
      [(bytes state.current.core.digest ++
          [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val], output)]
      (VerifierReply.single output) := by
  change MachineQueryPath
    (.query (bytes state.current.core.digest ++
      [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val]) fun answer =>
        .pure (VerifierReply.single answer)) _ _
  exact .query _ _ output [] (VerifierReply.single output) (.pure _)

theorem fixed_table_squeeze_reply_path
    (table : FixedOracleTable) (state : FutureFreeVerifierState)
    (owner : SqueezeOwner) (block : Nat) (output advance : Digest256)
    (outputLookup : tableLookup table
      (bytes state.current.core.digest ++ [domSqueeze]) = some output)
    (advanceLookup : tableLookup table
      (bytes state.current.core.digest ++ [domAdvance]) = some advance) :
    MachineQueryPath
      (futureFreeReplyProgram state (.squeezePair owner block))
      [(bytes state.current.core.digest ++ [domSqueeze], output),
       (bytes state.current.core.digest ++ [domAdvance], advance)]
      (VerifierReply.squeeze output advance) := by
  change MachineQueryPath
    (.query (bytes state.current.core.digest ++ [domSqueeze]) fun answer =>
      .query (bytes state.current.core.digest ++ [domAdvance]) fun next =>
        .pure (VerifierReply.squeeze answer next)) _ _
  exact .query _ _ output [_] _
    (.query _ _ advance [] _ (.pure _))

theorem structural_future_free_reply_path
    (state : FutureFreeVerifierState) (action : VerifierAction)
    (structural : structuralFutureFreeReply action =
      some VerifierReply.none) :
    MachineQueryPath (futureFreeReplyProgram state action) []
      VerifierReply.none := by
  cases action <;>
    simp_all [structuralFutureFreeReply, futureFreeReplyProgram]
  all_goals exact .pure VerifierReply.none

/-- A reply derived by the fixed-table ancestor runner gives a literal path
through the future-free reply program, and every pair on that path is backed
by the same table. -/
theorem derived_reply_gives_fixed_table_path
    (table : FixedOracleTable) (state : FutureFreeVerifierState)
    (action : VerifierAction) (reply : VerifierReply)
    (derived : deriveReply table state.current.bindings state.current.core
      action = some reply) :
    ∃ pairs,
      MachineQueryPath (futureFreeReplyProgram state action) pairs reply ∧
        PathUsesFixedTable table pairs := by
  cases action with
  | absorb payload =>
      let input := bytes state.current.core.digest ++
        [domAbsorb, payload.label] ++ payload.data
      change (tableLookup table input).bind
        (fun output => some (VerifierReply.single output)) = some reply at derived
      obtain ⟨output, lookup, result⟩ := Option.bind_eq_some_iff.mp derived
      have replyEq : VerifierReply.single output = reply :=
        Option.some.inj result
      subst reply
      refine ⟨[(input, output)], ?_,
        path_uses_fixed_table_cons table input output [] lookup
          (path_uses_fixed_table_nil table)⟩
      simpa [input] using
        fixed_table_absorb_reply_path table state payload output lookup
  | requestRootSalt tree =>
      let input := rootSaltInput state.current.bindings.context tree.tag
      change (tableLookup table input).bind
        (fun output => some (VerifierReply.single output)) = some reply at derived
      obtain ⟨output, lookup, result⟩ := Option.bind_eq_some_iff.mp derived
      have replyEq : VerifierReply.single output = reply :=
        Option.some.inj result
      subst reply
      refine ⟨[(input, output)], ?_,
        path_uses_fixed_table_cons table input output [] lookup
          (path_uses_fixed_table_nil table)⟩
      simpa [input] using
        fixed_table_root_salt_reply_path table state tree output lookup
  | absorbC1 root =>
      cases saved : state.current.core.c1Salt with
      | none =>
          simp [deriveReply, actionInputs, lookupSingleInput, saved] at derived
      | some salt =>
          let input := bytes state.current.core.digest ++
            [domAbsorb, c1RootLabel] ++
              (Payload.c1Root root.value salt).data
          simp only [deriveReply, actionInputs, saved, lookupSingleInput] at derived
          change (tableLookup table input).bind
            (fun output => some (VerifierReply.single output)) = some reply at derived
          obtain ⟨output, lookup, result⟩ :=
            Option.bind_eq_some_iff.mp derived
          have replyEq : VerifierReply.single output = reply :=
            Option.some.inj result
          subst reply
          refine ⟨[(input, output)], ?_,
            path_uses_fixed_table_cons table input output [] lookup
              (path_uses_fixed_table_nil table)⟩
          simpa [input] using fixed_table_absorb_c1_reply_path table state root
            salt output saved lookup
  | absorbC2 lambda chi commitment =>
      cases saved : state.current.core.c2Salt with
      | none =>
          simp [deriveReply, actionInputs, lookupSingleInput, saved] at derived
      | some salt =>
          let input := bytes state.current.core.digest ++
            [domAbsorb, c2RootLabel] ++
              (Payload.c2Root commitment.root salt).data
          simp only [deriveReply, actionInputs, saved, lookupSingleInput] at derived
          change (tableLookup table input).bind
            (fun output => some (VerifierReply.single output)) = some reply at derived
          obtain ⟨output, lookup, result⟩ :=
            Option.bind_eq_some_iff.mp derived
          have replyEq : VerifierReply.single output = reply :=
            Option.some.inj result
          subst reply
          refine ⟨[(input, output)], ?_,
            path_uses_fixed_table_cons table input output [] lookup
              (path_uses_fixed_table_nil table)⟩
          simpa [input] using fixed_table_absorb_c2_reply_path table state
            lambda chi commitment salt output saved lookup
  | squeezePair owner block =>
      let outputInput := bytes state.current.core.digest ++ [domSqueeze]
      let advanceInput := bytes state.current.core.digest ++ [domAdvance]
      change (tableLookup table outputInput).bind (fun output =>
        (tableLookup table advanceInput).bind fun advance =>
          some (VerifierReply.squeeze output advance)) = some reply at derived
      obtain ⟨output, outputLookup, derived⟩ :=
        Option.bind_eq_some_iff.mp derived
      obtain ⟨advance, advanceLookup, result⟩ :=
        Option.bind_eq_some_iff.mp derived
      have replyEq : VerifierReply.squeeze output advance = reply :=
        Option.some.inj result
      subst reply
      refine ⟨[(outputInput, output), (advanceInput, advance)], ?_, ?_⟩
      · simpa [outputInput, advanceInput] using
          fixed_table_squeeze_reply_path table state owner block output advance
            outputLookup advanceLookup
      · exact path_uses_fixed_table_cons table outputInput output _
          outputLookup
          (path_uses_fixed_table_cons table advanceInput advance []
            advanceLookup (path_uses_fixed_table_nil table))
  | workProbe stage nonce kind =>
      let input := bytes state.current.core.digest ++ [domGrind] ++ bytes nonce
      change (tableLookup table input).bind
        (fun output => some (VerifierReply.single output)) = some reply at derived
      obtain ⟨output, lookup, result⟩ := Option.bind_eq_some_iff.mp derived
      have replyEq : VerifierReply.single output = reply :=
        Option.some.inj result
      subst reply
      refine ⟨[(input, output)], ?_,
        path_uses_fixed_table_cons table input output [] lookup
          (path_uses_fixed_table_nil table)⟩
      simpa [input] using fixed_table_work_reply_path table state stage nonce
        kind output lookup
  | checkpoint checkpoint =>
      have replyEq : VerifierReply.none = reply := by
        change some VerifierReply.none = some reply at derived
        exact Option.some.inj derived
      subst reply
      exact ⟨[], structural_future_free_reply_path state _ rfl,
        path_uses_fixed_table_nil table⟩
  | markQ16Base =>
      have replyEq : VerifierReply.none = reply := by
        change some VerifierReply.none = some reply at derived
        exact Option.some.inj derived
      subst reply
      exact ⟨[], structural_future_free_reply_path state _ rfl,
        path_uses_fixed_table_nil table⟩
  | q16CandidateAbsorb counter outcome selected =>
      let input := bytes state.current.core.digest ++
        [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val]
      change (tableLookup table input).bind
        (fun output => some (VerifierReply.single output)) = some reply at derived
      obtain ⟨output, lookup, result⟩ := Option.bind_eq_some_iff.mp derived
      have replyEq : VerifierReply.single output = reply :=
        Option.some.inj result
      subst reply
      refine ⟨[(input, output)], ?_,
        path_uses_fixed_table_cons table input output [] lookup
          (path_uses_fixed_table_nil table)⟩
      change MachineQueryPath
        (.query input fun answer => .pure (VerifierReply.single answer))
        [(input, output)] (VerifierReply.single output)
      exact .query input _ output [] _ (.pure _)
  | q16Restore counter =>
      have replyEq : VerifierReply.none = reply := by
        change some VerifierReply.none = some reply at derived
        exact Option.some.inj derived
      subst reply
      exact ⟨[], structural_future_free_reply_path state _ rfl,
        path_uses_fixed_table_nil table⟩
  | q16Selected counter =>
      have replyEq : VerifierReply.none = reply := by
        change some VerifierReply.none = some reply at derived
        exact Option.some.inj derived
      subst reply
      exact ⟨[], structural_future_free_reply_path state _ rfl,
        path_uses_fixed_table_nil table⟩
  | q16SamplerAbortReject counter =>
      have replyEq : VerifierReply.none = reply := by
        change some VerifierReply.none = some reply at derived
        exact Option.some.inj derived
      subst reply
      exact ⟨[], structural_future_free_reply_path state _ rfl,
        path_uses_fixed_table_nil table⟩
  | q16AllNoncompactReject =>
      have replyEq : VerifierReply.none = reply := by
        change some VerifierReply.none = some reply at derived
        exact Option.some.inj derived
      subst reply
      exact ⟨[], structural_future_free_reply_path state _ rfl,
        path_uses_fixed_table_nil table⟩
  | terminal =>
      have replyEq : VerifierReply.none = reply := by
        change some VerifierReply.none = some reply at derived
        exact Option.some.inj derived
      subst reply
      exact ⟨[], structural_future_free_reply_path state _ rfl,
        path_uses_fixed_table_nil table⟩

/-- One action of a dependent fixed-table execution can be replayed by the
future-free driver when the live controller forces that action. -/
theorem fixed_table_action_is_raw_future_free_microstep
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state next : FutureFreeVerifierState)
    (action : VerifierAction) (reply : VerifierReply)
    (noSubmission : submitNextRawMessage raw state = none)
    (forced : state.current.control.nextVerifierAction? = some action)
    (derived : deriveReply table state.current.bindings state.current.core
      action = some reply)
    (advanced : advanceFutureFreeVerifier environment state reply = some next) :
    ∃ pairs,
      MachineQueryPath (rawFutureFreeMicrostep environment raw state)
        pairs next ∧
      PathUsesFixedTable table pairs := by
  obtain ⟨pairs, replyPath, supported⟩ :=
    derived_reply_gives_fixed_table_path table state action reply derived
  refine ⟨pairs, ?_, supported⟩
  have runnerEq : runOneFutureFreeVerifierAction environment state =
      bindOracleMachine (futureFreeReplyProgram state action) fun actualReply =>
        match advanceFutureFreeVerifier environment state actualReply with
        | some result => .pure result
        | none => .abort .controllerRefused := by
    unfold runOneFutureFreeVerifierAction
    split
    next noAction =>
      rw [forced] at noAction
      contradiction
    next actualAction actionFound =>
      have actionEq : actualAction = action :=
        Option.some.inj (actionFound.symm.trans forced)
      subst actualAction
      rfl
  simp only [rawFutureFreeMicrostep, noSubmission, runnerEq]
  have tailPath : MachineQueryPath
      (match advanceFutureFreeVerifier environment state reply with
      | some result => .pure result
      | none => .abort .controllerRefused) [] next := by
    rw [advanced]
    exact .pure next
  have combined := machine_query_path_bind_join _
    (fun actualReply =>
      match advanceFutureFreeVerifier environment state actualReply with
      | some result => .pure result
      | none => .abort .controllerRefused)
    pairs [] reply next replyPath tailPath
  simpa only [List.append_nil] using combined

theorem raw_submission_is_future_free_microstep
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state next : FutureFreeVerifierState)
    (submitted : submitNextRawMessage raw state = some next) :
    MachineQueryPath (rawFutureFreeMicrostep environment raw state) [] next := by
  simpa only [rawFutureFreeMicrostep, submitted] using
    MachineQueryPath.pure next

theorem advance_future_free_verifier_of_components
    (environment : FutureFreeEnvironment) (state : FutureFreeVerifierState)
    (action : VerifierAction) (reply : VerifierReply)
    (nextCore : RuntimeCore) (nextSnapshot : FutureFreeSnapshot)
    (forced : state.current.control.nextVerifierAction? = some action)
    (applied : applyActionWorkErased state.current.core action reply =
      some nextCore)
    (updated : afterFutureFreeVerifierReply environment state.current reply
      nextCore = some nextSnapshot) :
    advanceFutureFreeVerifier environment state reply =
      some (appendFutureFreeSnapshot state (.verifier action reply)
        nextSnapshot) := by
  rw [advanceFutureFreeVerifier]
  exact Option.bind_eq_some_iff.mpr ⟨action, forced,
    Option.bind_eq_some_iff.mpr ⟨nextCore, applied,
      Option.bind_eq_some_iff.mpr ⟨nextSnapshot, updated, rfl⟩⟩⟩

/-! ## Finite nonterminal driver prefixes -/

/-- A chronological sequence of actual raw-driver microsteps, none of whose
targets is a rejecting or terminal state.  The natural index counts all
prover and verifier microsteps; the pair list counts only oracle calls. -/
inductive NonterminalRawDriverTrace
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    FutureFreeVerifierState → Nat → List (ShaInput × ShaOutput) →
      FutureFreeVerifierState → Prop where
  | stop (state : FutureFreeVerifierState) :
      NonterminalRawDriverTrace environment raw state 0 [] state
  | next {state middle final : FutureFreeVerifierState}
      {head tail : List (ShaInput × ShaOutput)} {steps : Nat}
      (headPath : MachineQueryPath
        (rawFutureFreeMicrostep environment raw state) head middle)
      (middleNonterminal : isDriverHalt middle.current.control = false)
      (rest : NonterminalRawDriverTrace environment raw middle steps tail final) :
      NonterminalRawDriverTrace environment raw state (steps + 1)
        (head ++ tail) final

theorem fixed_table_action_gives_one_nonterminal_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state next : FutureFreeVerifierState)
    (action : VerifierAction) (reply : VerifierReply)
    (noSubmission : submitNextRawMessage raw state = none)
    (forced : state.current.control.nextVerifierAction? = some action)
    (derived : deriveReply table state.current.bindings state.current.core
      action = some reply)
    (advanced : advanceFutureFreeVerifier environment state reply = some next)
    (nonterminal : isDriverHalt next.current.control = false) :
    ∃ pairs,
      NonterminalRawDriverTrace environment raw state 1 pairs next ∧
        PathUsesFixedTable table pairs := by
  obtain ⟨pairs, path, supported⟩ :=
    fixed_table_action_is_raw_future_free_microstep table environment raw state
      next action reply noSubmission forced derived advanced
  refine ⟨pairs, ?_, supported⟩
  simpa using
    (NonterminalRawDriverTrace.next path nonterminal
      (NonterminalRawDriverTrace.stop next))

theorem raw_submission_gives_one_nonterminal_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state next : FutureFreeVerifierState)
    (submitted : submitNextRawMessage raw state = some next)
    (nonterminal : isDriverHalt next.current.control = false) :
    NonterminalRawDriverTrace environment raw state 1 [] next ∧
      PathUsesFixedTable table [] := by
  constructor
  · simpa using
      (NonterminalRawDriverTrace.next
        (raw_submission_is_future_free_microstep environment raw state next
          submitted)
        nonterminal (NonterminalRawDriverTrace.stop next))
  · exact path_uses_fixed_table_nil table

theorem nonterminal_raw_driver_trace_append
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (first middle final : FutureFreeVerifierState)
    (firstSteps secondSteps : Nat)
    (firstPairs secondPairs : List (ShaInput × ShaOutput))
    (left : NonterminalRawDriverTrace environment raw first firstSteps
      firstPairs middle)
    (right : NonterminalRawDriverTrace environment raw middle secondSteps
      secondPairs final) :
    NonterminalRawDriverTrace environment raw first
      (firstSteps + secondSteps) (firstPairs ++ secondPairs) final := by
  induction left with
  | stop state => simpa using right
  | @next state next middle head tail steps headPath nonterminal rest ih =>
      have combined :=
        NonterminalRawDriverTrace.next headPath nonterminal (ih right)
      have stepCount : (steps + secondSteps) + 1 =
          (steps + 1) + secondSteps := by omega
      rw [← stepCount]
      simpa only [List.append_assoc] using combined

theorem nonterminal_raw_driver_trace_has_machine_path
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state final : FutureFreeVerifierState) (steps : Nat)
    (pairs : List (ShaInput × ShaOutput))
    (trace : NonterminalRawDriverTrace environment raw state steps pairs final) :
    MachineQueryPath (driveRawFutureFree environment raw steps state)
      pairs final := by
  induction trace with
  | stop state => exact .pure state
  | @next state middle final head tail steps headPath nonterminal rest ih =>
      rw [show steps + 1 = Nat.succ steps by omega, driveRawFutureFree]
      apply machine_query_path_bind_join _ _ head tail middle final headPath
      simpa [nonterminal] using ih

theorem nonterminal_trace_then_terminal_step_has_machine_path
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages)
    (state before final : FutureFreeVerifierState) (steps : Nat)
    (prefixPairs lastPairs : List (ShaInput × ShaOutput))
    (prefixTrace : NonterminalRawDriverTrace environment raw state steps
      prefixPairs before)
    (last : MachineQueryPath
      (rawFutureFreeMicrostep environment raw before) lastPairs final)
    (terminal : isDriverHalt final.current.control = true) :
    MachineQueryPath (driveRawFutureFree environment raw (steps + 1) state)
      (prefixPairs ++ lastPairs) final := by
  induction prefixTrace with
  | stop state =>
      rw [show 0 + 1 = 1 by omega, driveRawFutureFree]
      have tail : MachineQueryPath
          (if _terminal : isDriverHalt final.current.control = true then
              .pure final
            else driveRawFutureFree environment raw 0 final)
          [] final := by
        simpa [terminal] using MachineQueryPath.pure final
      have combined := machine_query_path_bind_join _
        (fun next =>
          if _terminal : isDriverHalt next.current.control = true then .pure next
          else driveRawFutureFree environment raw 0 next)
        lastPairs [] final final last tail
      simpa only [List.nil_append, List.append_nil] using combined
  | @next state middle before head tail steps headPath nonterminal rest ih =>
      rw [show (steps + 1) + 1 = Nat.succ (steps + 1) by omega,
        driveRawFutureFree]
      have tailPath : MachineQueryPath
          (if _terminal : isDriverHalt middle.current.control = true then
              .pure middle
            else driveRawFutureFree environment raw (steps + 1) middle)
          (tail ++ lastPairs) final := by
        simpa [nonterminal] using ih last
      have combined := machine_query_path_bind_join _
        (fun next =>
          if _terminal : isDriverHalt next.current.control = true then .pure next
          else driveRawFutureFree environment raw (steps + 1) next)
        head (tail ++ lastPairs) middle final headPath tailPath
      simpa only [List.append_assoc] using combined

/-! ## Fixed adaptive-prefix actions -/

def tableExecutionLastCore
    {table : FixedOracleTable} {bindings : FixedBindings}
    {core : RuntimeCore} {actions : List VerifierAction}
    (trace : TableExecutionTrace table bindings core actions) : RuntimeCore :=
  match trace with
  | .done final => final
  | .step _ _ _ tail => tableExecutionLastCore tail

/-- Strengthened construction of the dependent table trace: unlike bare
`Nonempty`, this packages the final core computed by the runner. -/
theorem table_execution_trace_with_exact_last_of_run
    (table : FixedOracleTable) (bindings : FixedBindings)
    (actions : List VerifierAction) (core final : RuntimeCore)
    (run : runActionCores table bindings actions core = some final) :
    ∃ trace : TableExecutionTrace table bindings core actions,
      tableExecutionLastCore trace = final := by
  induction actions generalizing core with
  | nil =>
      have equal : core = final := by
        simpa [runActionCores] using run
      subst final
      exact ⟨.done core, rfl⟩
  | cons action rest ih =>
      rw [runActionCores] at run
      obtain ⟨next, actionRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      rw [runActionCore] at actionRun
      obtain ⟨reply, derived, applied⟩ :=
        Option.bind_eq_some_iff.mp actionRun
      obtain ⟨tail, last⟩ := ih (core := next) restRun
      exact ⟨.step reply derived applied tail, last⟩

/-- The control carried at a fixed-prefix boundary.  The empty suffix is
already the C1 prover-message gate; it is not a stuttering verifier phase. -/
def fixedPrefixBoundaryControl : List VerifierAction → OpenAdaptiveControl
  | [] => .awaitingC1
  | actions => .fixedPrefix actions

@[simp] theorem fixed_prefix_boundary_nil :
    fixedPrefixBoundaryControl [] = .awaitingC1 := rfl

@[simp] theorem fixed_prefix_boundary_cons
    (action : VerifierAction) (rest : List VerifierAction) :
    fixedPrefixBoundaryControl (action :: rest) =
      .fixedPrefix (action :: rest) := rfl

/-- A dependent fixed-table trace for the public fixed prefix replays as
actual nonterminal raw-driver steps.  The proof uses the replies and applied
cores stored in the trace; it does not ask for table coverage separately. -/
theorem fixed_prefix_table_trace_gives_raw_driver_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (bindings : FixedBindings)
    (core : RuntimeCore) (actions : List VerifierAction)
    (state : FutureFreeVerifierState)
    (trace : TableExecutionTrace table bindings core actions)
    (control : state.current.control =
      .adaptive (fixedPrefixBoundaryControl actions))
    (stateBindings : state.current.bindings = bindings)
    (stateCore : state.current.core = core) :
    ∃ steps pairs final,
      NonterminalRawDriverTrace environment raw state steps pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .adaptive .awaitingC1 ∧
      final.current.bindings = bindings ∧
      final.current.core = tableExecutionLastCore trace := by
  induction trace generalizing state with
  | done core =>
      refine ⟨0, [], state, .stop state, path_uses_fixed_table_nil table,
        ?_, stateBindings, ?_⟩
      · simpa using control
      · simpa [tableExecutionLastCore] using stateCore
  | @step core next action rest reply derived applied tail ih =>
      have controlHead : state.current.control =
          .adaptive (.fixedPrefix (action :: rest)) := by
        simpa using control
      have noSubmission : submitNextRawMessage raw state = none := by
        simp [submitNextRawMessage, controlHead]
      have forced : state.current.control.nextVerifierAction? = some action := by
        rw [controlHead]
        rfl
      have derivedState : deriveReply table state.current.bindings
          state.current.core action = some reply := by
        simpa [stateBindings, stateCore] using derived
      let nextSnapshot : FutureFreeSnapshot :=
        { state.current with
          control := .adaptive (fixedPrefixBoundaryControl rest)
          core := next }
      let nextState : FutureFreeVerifierState :=
        appendFutureFreeSnapshot state (.verifier action reply) nextSnapshot
      have advanced : advanceFutureFreeVerifier environment state reply =
          some nextState := by
        have appliedState : applyActionWorkErased state.current.core action reply =
            some next := by simpa [stateCore] using applied
        have updated : afterFutureFreeVerifierReply environment state.current
            reply next = some nextSnapshot := by
          cases rest <;>
            simp [afterFutureFreeVerifierReply,
              rawAfterFutureFreeVerifierReply, controlHead,
              OpenAdaptiveControl.afterVerifierReply,
              finishFixedPrefixControl, fixedPrefixBoundaryControl,
              nextSnapshot]
        simpa [nextState] using
          advance_future_free_verifier_of_components environment state action
            reply next nextSnapshot forced appliedState updated
      obtain ⟨headPairs, headPath, headSupported⟩ :=
        fixed_table_action_is_raw_future_free_microstep table environment raw
          state nextState action reply noSubmission forced derivedState advanced
      have nextControl : nextState.current.control =
          .adaptive (fixedPrefixBoundaryControl rest) := by
        rfl
      have nextBindings : nextState.current.bindings = bindings := by
        simpa [nextState, nextSnapshot, appendFutureFreeSnapshot,
          stateBindings]
      have nextCore : nextState.current.core = next := by rfl
      obtain ⟨tailSteps, tailPairs, final, tailTrace, tailSupported,
          finalControl, finalBindings, finalCore⟩ :=
        ih nextState nextControl nextBindings nextCore
      have nextNonterminal : isDriverHalt nextState.current.control = false := by
        rw [nextControl]
        cases rest <;> rfl
      refine ⟨tailSteps + 1, headPairs ++ tailPairs, final,
        .next headPath nextNonterminal tailTrace,
        path_uses_fixed_table_append table headPairs tailPairs headSupported
          tailSupported,
        finalControl, finalBindings, ?_⟩
      simpa [tableExecutionLastCore] using finalCore

/-- Executability of a fixed-prefix action list is enough to obtain the raw
driver trace.  The dependent table trace, including every exact reply, is
constructed from the run rather than supplied by the caller. -/
theorem fixed_prefix_run_gives_raw_driver_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (bindings : FixedBindings)
    (core finalCore : RuntimeCore) (actions : List VerifierAction)
    (state : FutureFreeVerifierState)
    (run : runActionCores table bindings actions core = some finalCore)
    (control : state.current.control =
      .adaptive (fixedPrefixBoundaryControl actions))
    (stateBindings : state.current.bindings = bindings)
    (stateCore : state.current.core = core) :
    ∃ steps pairs final,
      NonterminalRawDriverTrace environment raw state steps pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .adaptive .awaitingC1 ∧
      final.current.bindings = bindings ∧
      final.current.core = finalCore := by
  obtain ⟨trace, last⟩ := table_execution_trace_with_exact_last_of_run
    table bindings actions core finalCore run
  obtain ⟨steps, pairs, final, path, supported, finalControl,
      finalBindings, finalCoreEq⟩ :=
    fixed_prefix_table_trace_gives_raw_driver_trace table environment raw
      bindings core actions state trace control stateBindings stateCore
  exact ⟨steps, pairs, final, path, supported, finalControl, finalBindings,
    finalCoreEq.trans last⟩

/-- The checked refinement's actual public fixed prefix reaches the unique C1
message gate of the future-free controller.  Besides the exact oracle path,
the conclusion retains the deterministic evaluator digest and the fact that
none of the later saved fields has been installed early. -/
theorem prefix_before_c1_run_gives_future_free_trace
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (beforeC1 : EvalState)
    (run : runMachineEventsWorkErased table
      (prefixBeforeC1 tape.messages) initialEvalState = some beforeC1) :
    ∃ steps pairs final,
      NonterminalRawDriverTrace (fixedTapeFutureFreeEnvironment tape)
        (fixedTapeRawMessages tape)
        (initialFutureFreeVerifierState
          (FixedBindings.ofContext tape.messages.context))
        steps pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .adaptive .awaitingC1 ∧
      SameDigest final.current.core beforeC1 ∧
      final.current.core.c1Salt = none ∧
      final.current.core.c2Salt = none ∧
      final.current.core.q16Base = none := by
  let bindings := FixedBindings.ofContext tape.messages.context
  obtain ⟨beforeCore, actionRun, same, c1Salt, c2Salt, q16Base⟩ :=
    machine_events_actions_agree table bindings
      (prefixBeforeC1 tape.messages) initialCore initialEvalState beforeC1 rfl
      run
  let initial := initialFutureFreeVerifierState bindings
  have initialControl : initial.current.control =
      .adaptive
        (fixedPrefixBoundaryControl
          (eventsToActions (prefixBeforeC1 tape.messages))) := by
    simp [initial, bindings, initialFutureFreeVerifierState,
      initialFutureFreeSnapshot, fixed_bindings_recover_context,
      fixedPrefixBoundaryControl, openFixedPrefixActions, prefixBeforeC1,
      eventsToActions, eventActions] <;> rfl
  have initialBindings : initial.current.bindings = bindings := by rfl
  have initialCoreEq : initial.current.core = initialCore := by rfl
  obtain ⟨steps, pairs, final, trace, supported, finalControl,
      _finalBindings, finalCore⟩ :=
    fixed_prefix_run_gives_raw_driver_trace table
      (fixedTapeFutureFreeEnvironment tape) (fixedTapeRawMessages tape)
      bindings initialCore beforeCore
      (eventsToActions (prefixBeforeC1 tape.messages)) initial actionRun
      initialControl initialBindings initialCoreEq
  refine ⟨steps, pairs, final, trace, supported, finalControl, ?_, ?_, ?_, ?_⟩
  · rw [finalCore]
    exact same
  · rw [finalCore]
    exact c1Salt.trans rfl
  · rw [finalCore]
    exact c2Salt.trans rfl
  · rw [finalCore]
    exact q16Base.trans rfl

/-- A strict checked fixed-tape refinement therefore reaches the operational
C1 gate through a fixed-table-backed raw-driver prefix.  This is a genuine
partial bisimulation theorem; it does not yet claim the later adaptive and
q16 phases. -/
theorem checked_refinement_reaches_future_free_c1_gate
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (rawTrace : InteractiveRawTrace)
    (run : checkedRefine table exactDeterministicDecoders tape =
      some rawTrace) :
    ∃ steps pairs final,
      NonterminalRawDriverTrace (fixedTapeFutureFreeEnvironment tape)
        (fixedTapeRawMessages tape)
        (initialFutureFreeVerifierState
          (FixedBindings.ofContext tape.messages.context))
        steps pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .adaptive .awaitingC1 ∧
      final.current.core.c1Salt = none ∧
      final.current.core.c2Salt = none ∧
      final.current.core.q16Base = none := by
  have erasedChecked : checkedRefineWorkErased table
      exactDeterministicDecoders tape = some rawTrace :=
    checked_refinement_success_survives_work_erasure table
      exactDeterministicDecoders tape rawTrace run
  have erasedRun : refineWorkErased table tape = some rawTrace :=
    checked_refine_work_erased_forgets_check table exactDeterministicDecoders
      tape rawTrace erasedChecked
  rw [refineWorkErased] at erasedRun
  obtain ⟨prefixState, prefixRun, _rest⟩ :=
    Option.bind_eq_some_iff.mp erasedRun
  rw [runPrefixWorkErased] at prefixRun
  obtain ⟨beforeC1, beforeRun, _afterC1⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨steps, pairs, final, trace, supported, control, _same,
      c1Salt, c2Salt, q16Base⟩ :=
    prefix_before_c1_run_gives_future_free_trace table tape beforeC1 beforeRun
  exact ⟨steps, pairs, final, trace, supported, control, c1Salt, c2Salt,
    q16Base⟩

/-! ## The adaptive C1/lambda/chi/C2 segment -/

/-- At the C1 gate the only raw prover transition installs the exact typed C1
root.  It is a zero-query, nonterminal driver step and preserves the complete
runtime core and fixed bindings. -/
theorem awaiting_c1_submits_exact_raw_root
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (atC1 : state.current.control = .adaptive .awaitingC1) :
    ∃ next,
      NonterminalRawDriverTrace environment raw state 1 [] next ∧
      PathUsesFixedTable table [] ∧
      next.current.control =
        .adaptive (.requestC1Salt (rawC1Root raw)) ∧
      next.current.core = state.current.core ∧
      next.current.bindings = state.current.bindings := by
  let snapshot : FutureFreeSnapshot :=
    { state.current with
      control := .adaptive (.requestC1Salt (rawC1Root raw))
      c1Root := some (rawC1Root raw).value }
  let next := appendFutureFreeSnapshot state
    (.proverC1 (rawC1Root raw)) snapshot
  have submitted : submitNextRawMessage raw state = some next := by
    unfold submitNextRawMessage
    split <;> simp_all [submitFutureFreeC1, snapshot, next]
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  obtain ⟨trace, supported⟩ :=
    raw_submission_gives_one_nonterminal_trace table environment raw state next
      submitted nonterminal
  exact ⟨next, trace, supported, rfl, rfl, rfl⟩

/-- The C1 salt request is the literal public-root-salt table call.  It does
not advance the duplex digest and moves the controller only to the C1 absorb
phase. -/
theorem c1_root_salt_run_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before withSalt : EvalState) (salt : Digest256)
    (atRequest : state.current.control =
      .adaptive (.requestC1Salt (rawC1Root raw)))
    (bindings : state.current.bindings = FixedBindings.ofContext raw.context)
    (same : SameDigest state.current.core before)
    (run : rootSaltStep table before raw.context c1TreeTag =
      some (salt, withSalt)) :
    ∃ pairs next,
      NonterminalRawDriverTrace environment raw state 1 pairs next ∧
      PathUsesFixedTable table pairs ∧
      next.current.control = .adaptive (.absorbC1 (rawC1Root raw)) ∧
      next.current.core =
        { state.current.core with c1Salt := some salt } ∧
      SameDigest next.current.core withSalt := by
  obtain ⟨lookup, _calls, digest⟩ := query_step_appends_one table before
    withSalt (.publicRootSalt raw.context c1TreeTag) salt run
  have normalized : tableLookup table
      (rootSaltInput raw.context c1TreeTag) = some salt := by
    simpa only [RawQueryRole.input] using lookup
  have derived : deriveReply table state.current.bindings state.current.core
      (.requestRootSalt .initialC1) = some (.single salt) := by
    rw [bindings]
    simp only [deriveReply, actionInputs, lookupSingleInput,
      fixed_bindings_recover_context, AuthenticatedTree.tag]
    rw [normalized]
    rfl
  let nextCore : RuntimeCore :=
    { state.current.core with c1Salt := some salt }
  have applied : applyActionWorkErased state.current.core
      (.requestRootSalt .initialC1) (.single salt) = some nextCore := by
    rfl
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with
      control := .adaptive (.absorbC1 (rawC1Root raw))
      core := nextCore }
  let next := appendFutureFreeSnapshot state
    (.verifier (.requestRootSalt .initialC1) (.single salt)) nextSnapshot
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atRequest]
  have forced : state.current.control.nextVerifierAction? =
      some (.requestRootSalt .initialC1) := by
    rw [atRequest]
    rfl
  have advanced : advanceFutureFreeVerifier environment state (.single salt) =
      some next := by
    have updated : afterFutureFreeVerifierReply environment state.current
        (.single salt) nextCore = some nextSnapshot := by
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        atRequest, OpenAdaptiveControl.afterVerifierReply, nextSnapshot]
    simpa [next] using
      advance_future_free_verifier_of_components environment state
        (.requestRootSalt .initialC1) (.single salt) nextCore nextSnapshot
        forced applied updated
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  obtain ⟨pairs, trace, supported⟩ :=
    fixed_table_action_gives_one_nonterminal_trace table environment raw state
      next (.requestRootSalt .initialC1) (.single salt) noSubmission forced
      derived advanced nonterminal
  refine ⟨pairs, next, trace, supported, rfl, rfl, ?_⟩
  change state.current.core.digest = withSalt.digest
  have unchanged : withSalt.digest = before.digest := by
    simpa only [RawQueryRole.nextDigest] using digest
  exact same.trans unchanged.symm

/-- The following C1 absorb uses the saved salt and exact 208-bit raw root,
then opens the incremental lambda sampler. -/
theorem c1_absorb_run_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before after : EvalState) (salt : Digest256)
    (atAbsorb : state.current.control =
      .adaptive (.absorbC1 (rawC1Root raw)))
    (saved : state.current.core.c1Salt = some salt)
    (same : SameDigest state.current.core before)
    (run : absorbStep table before
      (.c1Root (rawC1Root raw).value salt) = some after) :
    ∃ pairs next,
      NonterminalRawDriverTrace environment raw state 1 pairs next ∧
      PathUsesFixedTable table pairs ∧
      next.current.control = .adaptive (.sampleLambda []) ∧
      next.current.core =
        { state.current.core with digest := after.digest } ∧
      SameDigest next.current.core after := by
  rw [absorbStep] at run
  obtain ⟨queryResult, queryRun, result⟩ := Option.bind_eq_some_iff.mp run
  rcases queryResult with ⟨output, stepped⟩
  have steppedEq : stepped = after := by
    simpa only [pure, Option.some.injEq] using result
  subst stepped
  obtain ⟨lookup, _calls, digest⟩ := query_step_appends_one table before
    after (.absorb (.c1Root (rawC1Root raw).value salt)) output queryRun
  have outputEq : output = after.digest := by
    simpa only [RawQueryRole.nextDigest] using digest.symm
  subst output
  have normalized : tableLookup table
      (bytes before.digest ++ [domAbsorb, c1RootLabel] ++
        (Payload.c1Root (rawC1Root raw).value salt).data) =
      some after.digest := by
    simpa only [RawQueryRole.input, Payload.label] using lookup
  have derived : deriveReply table state.current.bindings state.current.core
      (.absorbC1 (rawC1Root raw)) = some (.single after.digest) := by
    simp only [deriveReply, actionInputs, saved, lookupSingleInput]
    change state.current.core.digest = before.digest at same
    rw [same, normalized]
    rfl
  let nextCore : RuntimeCore :=
    { state.current.core with digest := after.digest }
  have applied : applyActionWorkErased state.current.core
      (.absorbC1 (rawC1Root raw)) (.single after.digest) = some nextCore := by
    simp [applyActionWorkErased, saved, nextCore]
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with
      control := .adaptive (.sampleLambda [])
      core := nextCore }
  let next := appendFutureFreeSnapshot state
    (.verifier (.absorbC1 (rawC1Root raw)) (.single after.digest))
    nextSnapshot
  have noSubmission : submitNextRawMessage raw state = none := by
    simp [submitNextRawMessage, atAbsorb]
  have forced : state.current.control.nextVerifierAction? =
      some (.absorbC1 (rawC1Root raw)) := by
    rw [atAbsorb]
    rfl
  have advanced : advanceFutureFreeVerifier environment state
      (.single after.digest) = some next := by
    have updated : afterFutureFreeVerifierReply environment state.current
        (.single after.digest) nextCore = some nextSnapshot := by
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        atAbsorb, OpenAdaptiveControl.afterVerifierReply, nextSnapshot]
    simpa [next] using
      advance_future_free_verifier_of_components environment state
        (.absorbC1 (rawC1Root raw)) (.single after.digest) nextCore
        nextSnapshot forced applied updated
  have nonterminal : isDriverHalt next.current.control = false := by rfl
  obtain ⟨pairs, trace, supported⟩ :=
    fixed_table_action_gives_one_nonterminal_trace table environment raw state
      next (.absorbC1 (rawC1Root raw)) (.single after.digest) noSubmission
      forced derived advanced nonterminal
  exact ⟨pairs, next, trace, supported, rfl, rfl, rfl⟩

/-- An evaluator squeeze supplies exactly the future-free atomic reply: the
returned block comes from `S || 01`, while the installed digest and second
pair component come from `S || 02`. -/
theorem evaluator_squeeze_derives_exact_future_free_reply
    (table : FixedOracleTable) (state : FutureFreeVerifierState)
    (before after : EvalState) (owner : SqueezeOwner) (block : Nat)
    (output : Digest256) (same : SameDigest state.current.core before)
    (run : squeezeStep table before owner block = some (output, after)) :
    deriveReply table state.current.bindings state.current.core
        (.squeezePair owner block) = some (.squeeze output after.digest) ∧
      applyActionWorkErased state.current.core (.squeezePair owner block)
        (.squeeze output after.digest) =
          some { state.current.core with digest := after.digest } ∧
      ∃ pairs,
        MachineQueryPath
          (futureFreeReplyProgram state (.squeezePair owner block)) pairs
          (.squeeze output after.digest) ∧
        PathUsesFixedTable table pairs := by
  obtain ⟨outputLookup, advanceLookup, _calls⟩ :=
    squeeze_step_emits_two_distinct_queries table before after owner block
      output run
  change tableLookup table (bytes before.digest ++ [domSqueeze]) =
    some output at outputLookup
  change tableLookup table (bytes before.digest ++ [domAdvance]) =
    some after.digest at advanceLookup
  have derived : deriveReply table state.current.bindings state.current.core
      (.squeezePair owner block) = some (.squeeze output after.digest) := by
    simp only [deriveReply, actionInputs]
    change state.current.core.digest = before.digest at same
    rw [same, outputLookup, advanceLookup]
    rfl
  have applied : applyActionWorkErased state.current.core
      (.squeezePair owner block) (.squeeze output after.digest) =
        some { state.current.core with digest := after.digest } := by
    rfl
  let outputInput := bytes state.current.core.digest ++ [domSqueeze]
  let advanceInput := bytes state.current.core.digest ++ [domAdvance]
  have outputLookupState : tableLookup table outputInput = some output := by
    change tableLookup table
      (bytes state.current.core.digest ++ [domSqueeze]) = some output
    rw [same]
    exact outputLookup
  have advanceLookupState : tableLookup table advanceInput =
      some after.digest := by
    change tableLookup table
      (bytes state.current.core.digest ++ [domAdvance]) = some after.digest
    rw [same]
    exact advanceLookup
  refine ⟨derived, applied,
    [(outputInput, output), (advanceInput, after.digest)], ?_, ?_⟩
  · simpa [outputInput, advanceInput] using
      fixed_table_squeeze_reply_path table state owner block output after.digest
        outputLookupState advanceLookupState
  · exact path_uses_fixed_table_cons table outputInput output _
      outputLookupState
      (path_uses_fixed_table_cons table advanceInput after.digest []
        advanceLookupState (path_uses_fixed_table_nil table))

def controlAfterOpenAdaptiveReply
    (next : OpenAdaptiveControl) : FutureFreeControl :=
  match next with
  | .afterAdaptiveC2 _ _ => .linear fullFutureFreeSlots
  | _ => .adaptive next

def decodedAfterOpenAdaptiveReply (snapshot : FutureFreeSnapshot)
    (before after : OpenAdaptiveControl) : List DecodedChallenge :=
  match before, after with
  | .sampleLambda _, .sampleChi lambda _ =>
      snapshot.decodedChallenges ++ [{ id := .lambda, value := lambda }]
  | .sampleChi _ _, .awaitingC2 _ chi =>
      snapshot.decodedChallenges ++ [{ id := .chi, value := chi }]
  | _, _ => snapshot.decodedChallenges

/-- One incremental early challenge block is an actual atomic two-query
driver step.  Its successor is computed by the concrete open adaptive
decoder; no challenge value or stopping point is supplied by this theorem. -/
theorem open_adaptive_squeeze_run_gives_future_free_step
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before after : EvalState) (control nextControl : OpenAdaptiveControl)
    (owner : SqueezeOwner) (block : Nat) (output : Digest256)
    (atControl : state.current.control = .adaptive control)
    (forcedOpen : control.nextVerifierAction? =
      some (.squeezePair owner block))
    (same : SameDigest state.current.core before)
    (run : squeezeStep table before owner block = some (output, after))
    (noSubmission : submitNextRawMessage raw state = none)
    (decoded : control.afterVerifierReply environment.decoders
      (.squeeze output after.digest) = some nextControl)
    (nonterminal : isDriverHalt
      (controlAfterOpenAdaptiveReply nextControl) = false) :
    ∃ pairs next,
      NonterminalRawDriverTrace environment raw state 1 pairs next ∧
      PathUsesFixedTable table pairs ∧
      next.current.control = controlAfterOpenAdaptiveReply nextControl ∧
      next.current.core =
        { state.current.core with digest := after.digest } ∧
      SameDigest next.current.core after := by
  obtain ⟨derived, applied, _pairs, _replyPath, _supported⟩ :=
    evaluator_squeeze_derives_exact_future_free_reply table state before after
      owner block output same run
  have forced : state.current.control.nextVerifierAction? =
      some (.squeezePair owner block) := by
    rw [atControl]
    exact forcedOpen
  let nextCore : RuntimeCore :=
    { state.current.core with digest := after.digest }
  let nextSnapshot : FutureFreeSnapshot :=
    { state.current with
      control := controlAfterOpenAdaptiveReply nextControl
      core := nextCore
      decodedChallenges :=
        decodedAfterOpenAdaptiveReply state.current control nextControl }
  let next := appendFutureFreeSnapshot state
    (.verifier (.squeezePair owner block) (.squeeze output after.digest))
    nextSnapshot
  have advanced : advanceFutureFreeVerifier environment state
      (.squeeze output after.digest) = some next := by
    have updated : afterFutureFreeVerifierReply environment state.current
        (.squeeze output after.digest) nextCore = some nextSnapshot := by
      simp [afterFutureFreeVerifierReply, rawAfterFutureFreeVerifierReply,
        atControl, decoded, controlAfterOpenAdaptiveReply,
        decodedAfterOpenAdaptiveReply, nextCore, nextSnapshot] <;>
        (constructor <;> rfl)
    simpa [next] using
      advance_future_free_verifier_of_components environment state
        (.squeezePair owner block) (.squeeze output after.digest) nextCore
        nextSnapshot forced applied updated
  have nextNonterminal : isDriverHalt next.current.control = false := by
    change isDriverHalt (controlAfterOpenAdaptiveReply nextControl) = false
    exact nonterminal
  obtain ⟨pairs, trace, supported⟩ :=
    fixed_table_action_gives_one_nonterminal_trace table environment raw state
      next (.squeezePair owner block) (.squeeze output after.digest)
      noSubmission forced derived advanced
      nextNonterminal
  exact ⟨pairs, next, trace, supported, rfl, rfl, rfl⟩

/-- The whole adaptive C1 message/salt/absorb round is three raw-driver
microsteps and ends exactly at the empty lambda accumulator. -/
theorem c1_round_run_gives_future_free_trace
    (table : FixedOracleTable) (environment : FutureFreeEnvironment)
    (raw : RawTag73ProverMessages) (state : FutureFreeVerifierState)
    (before withSalt after : EvalState) (salt : Digest256)
    (atC1 : state.current.control = .adaptive .awaitingC1)
    (bindings : state.current.bindings = FixedBindings.ofContext raw.context)
    (same : SameDigest state.current.core before)
    (saltRun : rootSaltStep table before raw.context c1TreeTag =
      some (salt, withSalt))
    (absorbRun : absorbStep table withSalt
      (.c1Root (rawC1Root raw).value salt) = some after) :
    ∃ pairs final,
      NonterminalRawDriverTrace environment raw state 3 pairs final ∧
      PathUsesFixedTable table pairs ∧
      final.current.control = .adaptive (.sampleLambda []) ∧
      SameDigest final.current.core after := by
  obtain ⟨submitted, submissionTrace, submissionSupported,
      submittedControl, submittedCore, submittedBindings⟩ :=
    awaiting_c1_submits_exact_raw_root table environment raw state atC1
  have submittedBinding : submitted.current.bindings =
      FixedBindings.ofContext raw.context := submittedBindings.trans bindings
  have submittedSame : SameDigest submitted.current.core before := by
    rw [submittedCore]
    exact same
  obtain ⟨saltPairs, salted, saltTrace, saltSupported, saltedControl,
      saltedCore, saltedSame⟩ :=
    c1_root_salt_run_gives_future_free_step table environment raw submitted
      before withSalt salt submittedControl submittedBinding submittedSame
      saltRun
  have saltedSaved : salted.current.core.c1Salt = some salt := by
    rw [saltedCore]
  obtain ⟨absorbPairs, final, absorbTrace, absorbSupported, finalControl,
      _finalCore, finalSame⟩ :=
    c1_absorb_run_gives_future_free_step table environment raw salted withSalt
      after salt saltedControl saltedSaved saltedSame absorbRun
  have firstTwo : NonterminalRawDriverTrace environment raw state 2
      ([] ++ saltPairs) salted := by
    simpa using nonterminal_raw_driver_trace_append environment raw state
      submitted salted 1 1 [] saltPairs submissionTrace saltTrace
  have allThree : NonterminalRawDriverTrace environment raw state 3
      (([] ++ saltPairs) ++ absorbPairs) final := by
    simpa using nonterminal_raw_driver_trace_append environment raw state
      salted final 2 1 ([] ++ saltPairs) absorbPairs firstTwo absorbTrace
  refine ⟨([] ++ saltPairs) ++ absorbPairs, final, allThree, ?_,
    finalControl, finalSame⟩
  exact path_uses_fixed_table_append table ([] ++ saltPairs) absorbPairs
    (path_uses_fixed_table_append table [] saltPairs submissionSupported
      saltSupported) absorbSupported

/-! The protocol-specific checked-refinement construction follows below. -/

#print axioms fixed_table_action_is_raw_future_free_microstep
#print axioms checked_refinement_reaches_future_free_c1_gate
#print axioms c1_round_run_gives_future_free_trace
#print axioms open_adaptive_squeeze_run_gives_future_free_step

end

end AspisK1.V7Tag73CheckedRefinementFutureFreePath
