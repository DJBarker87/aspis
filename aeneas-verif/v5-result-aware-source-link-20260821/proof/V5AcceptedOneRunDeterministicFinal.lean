import V5AcceptedOneRunDeterministicClosure
import V5AcceptedSnapshotMainDotExact

/-!
# Complete deterministic result for one accepted snapshot

The two implementation facts needed by the earlier assembly theorem are
proved by the imported compact-fold and main-accumulator modules.  They are
used inside the proofs below, so callers supply only the ordinary cryptographic
and released-schedule premises of the security statement.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace AspisV5AcceptedOneRunDeterministicFinal

open Aeneas Aeneas.Std Result
open AspisV5AcceptedClaimTableExact
open AspisV5AcceptedDeterministicRelationTail
open AspisV5AcceptedOneRunDeterministicClosure
open AspisV5AcceptedOneRunSecurityClosure
open AspisV5AcceptedSameRunRelationFriSnapshot
open AspisV5RelationStressSourceBridge

abbrev K := AspisV5FriAcceptedForestChecks.K

/-- One accepted production snapshot determines the complete maintained
relation caller.  The compact folds and the main accumulator are derived from
that same accepted execution; neither is a premise of this theorem. -/
theorem accepted_snapshot_exact_deterministic_caller
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    AcceptedSnapshotExactDeterministicCaller snapshot := by
  obtain ⟨mainWeights, mainDotExact⟩ :=
    AspisV5AcceptedSnapshotMainDotExact.accepted_snapshot_main_dot_exact
      snapshot
  exact accepted_snapshot_exact_deterministic_caller_of_main_dot snapshot
    mainWeights mainDotExact

/-- Security conclusion for one accepted production snapshot.  The theorem
does not ask the caller for a compact-fold equality, a main-weight schedule,
or a main-dot witness. -/
theorem accepted_snapshot_security_conclusion
    (rc : AspisFormal.HashMerkleModel.RoundConstants)
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
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (hhash :
      AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
        sha256 V5AcceptedEntryGenerated.verify.sbf_hashv_totalized)
    (base : AspisV5ComponentCConcreteFoldLinearity.FixedSchedule
      (ZMod AspisCircleGroupOrder.P) K)
    (hproduction :
      AspisV5AcceptedExecutionReleasedSchedule.ProductionUsesReleasedFriTables
        base)
    (hpublished :
      AspisV5FriPublishedOutputEncoderDecoding.PublishedOrdinaryPolynomialCurveDecoding
        (K := K))
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    ∃ mainWeights : SourceMainWeightSchedule K,
      AcceptedSnapshotSecurityConclusion rc deployedOwner deployedNote
        deployedNullifier deployedNode sha256 base snapshot
        (acceptedSnapshotPartialCallerData snapshot
          (acceptedPointClaimTable parsed.relation_claims) mainWeights) := by
  apply accepted_snapshot_security_conclusion_of_exact_caller rc sha256 hhash
    base hproduction hpublished snapshot
  exact accepted_snapshot_exact_deterministic_caller snapshot

/-- Start from one successful extracted production verifier call, build its
single-run snapshot, and derive the deterministic security conclusion.  The
caller does not provide any relation-fold, accumulator, or model-agreement
witness. -/
theorem accepted_composite_security_conclusion
    (rc : AspisFormal.HashMerkleModel.RoundConstants)
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
    (terminalBoundary :
      AspisV5AcceptedEntrySourceBridge.EntryTerminalBoundary)
    (accountData : Slice Std.U8)
    (parsed : SnapshotEntryParsed)
    (liveStatement : SnapshotEntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : SnapshotEntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement
          terminalBoundary accountData parsed liveStatement statementDigest =
        .ok (.Ok acceptedValue))
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (hhash :
      AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
        sha256 V5AcceptedEntryGenerated.verify.sbf_hashv_totalized)
    (base : AspisV5ComponentCConcreteFoldLinearity.FixedSchedule
      (ZMod AspisCircleGroupOrder.P) K)
    (hproduction :
      AspisV5AcceptedExecutionReleasedSchedule.ProductionUsesReleasedFriTables
        base)
    (hpublished :
      AspisV5FriPublishedOutputEncoderDecoding.PublishedOrdinaryPolynomialCurveDecoding
        (K := K)) :
    ∃ snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
        liveStatement statementDigest acceptedValue,
      ∃ mainWeights : SourceMainWeightSchedule K,
        AcceptedSnapshotSecurityConclusion rc deployedOwner deployedNote
          deployedNullifier deployedNode sha256 base snapshot
          (acceptedSnapshotPartialCallerData snapshot
            (acceptedPointClaimTable parsed.relation_claims) mainWeights) := by
  obtain ⟨snapshot⟩ :=
    accepted_composite_builds_same_run_relation_fri_snapshot terminalBoundary
      accountData parsed liveStatement statementDigest acceptedValue success
  refine ⟨snapshot, ?_⟩
  exact accepted_snapshot_security_conclusion rc sha256 hhash base hproduction
    hpublished snapshot

/-! ## Terminal-evaluator independence

The extracted outer verifier represents the production terminal evaluator as
an explicit function boundary.  The security argument above does not use that
evaluator's model equality: after the terminal gate succeeds, the independently
checked relation and FRI phases are sufficient.  We can therefore quantify over
an arbitrary evaluator and build the boundary reflexively. -/

abbrev EntryTerminalEvaluator :=
  V5AtomicTerminalPrefixWrapperCompleteGenerated.aspis_statement.atomic_state_only_terminal.V5TerminalEvaluator

@[reducible] def reflexiveTerminalBoundary
    (evaluator : EntryTerminalEvaluator) :
    AspisV5AcceptedEntrySourceBridge.EntryTerminalBoundary where
  compiledEvaluator := evaluator
  maintainedModel := evaluator
  exactSourceModelEquality := rfl

/-- The complete accepted-call theorem holds for every behavior of the opaque
terminal evaluator.  In particular, no evaluator-to-model equality is a
premise of the released verifier's soundness path. -/
theorem accepted_composite_security_conclusion_for_any_terminal_evaluator
    (rc : AspisFormal.HashMerkleModel.RoundConstants)
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
    (terminalEvaluator : EntryTerminalEvaluator)
    (accountData : Slice Std.U8)
    (parsed : SnapshotEntryParsed)
    (liveStatement : SnapshotEntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : SnapshotEntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement
          (reflexiveTerminalBoundary terminalEvaluator) accountData parsed
          liveStatement statementDigest = .ok (.Ok acceptedValue))
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (hhash :
      AspisV5MerkleUnchangedFullHelperBridge.HashCallbackEqualsSha256
        sha256 V5AcceptedEntryGenerated.verify.sbf_hashv_totalized)
    (base : AspisV5ComponentCConcreteFoldLinearity.FixedSchedule
      (ZMod AspisCircleGroupOrder.P) K)
    (hpublished :
      AspisV5FriPublishedOutputEncoderDecoding.PublishedOrdinaryPolynomialCurveDecoding
        (K := K)) :
    ∃ snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
        liveStatement statementDigest acceptedValue,
      ∃ mainWeights : SourceMainWeightSchedule K,
        AcceptedSnapshotSecurityConclusion rc deployedOwner deployedNote
          deployedNullifier deployedNode sha256
          (AspisV5AcceptedExecutionReleasedSchedule.exactReleasedFriTables
            base) snapshot
          (acceptedSnapshotPartialCallerData snapshot
            (acceptedPointClaimTable parsed.relation_claims) mainWeights) := by
  exact accepted_composite_security_conclusion rc
    (reflexiveTerminalBoundary terminalEvaluator) accountData parsed
    liveStatement statementDigest acceptedValue success sha256 hhash
    (AspisV5AcceptedExecutionReleasedSchedule.exactReleasedFriTables base)
    (AspisV5AcceptedExecutionReleasedSchedule.exactReleasedFriTables_source_shape
      base)
    hpublished

#print axioms accepted_snapshot_exact_deterministic_caller
#print axioms accepted_snapshot_security_conclusion
#print axioms accepted_composite_security_conclusion
#print axioms
  accepted_composite_security_conclusion_for_any_terminal_evaluator

end AspisV5AcceptedOneRunDeterministicFinal
