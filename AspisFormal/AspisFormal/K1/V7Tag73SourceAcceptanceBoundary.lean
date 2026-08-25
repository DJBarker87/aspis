import AspisFormal.K1.V7Tag73DeterministicRefinement

/-!
# Deployed-source acceptance boundary for `checkedRefine`

The strongest archived Charon/Aeneas result-flow theorem is
`AspisV7ProductionRootSourceBridge.deployedRoot_success_exact` in the
separate `v7-onefold-accepted-source-20260825` replay project.  It proves that
successful generated parser, public-key/schedule, and opaque transcript-call
interfaces make the byte-identical deployed root return the exact verified
transcript and folded-query projection.  Its two companion theorems prove
parser and transcript rejection fail closed.

That theorem does not connect the opaque transcript-call interface to
`checkedRefine`.  In particular, Aeneas leaves
`verify_v7_compact_transcript_and_relation_prepared` opaque, together with its
terminal callback, two-tree authentication/query folding, relation arithmetic,
and final terminal equality.  Charon/Aeneas translation correctness may
transport the generated root semantics to Rust; it cannot supply semantics
for those opaque callees.

This module kernel-checks the exact main-project side of the boundary.  A
successful `checkedRefine` exposes deterministic hash replay plus decoder
well-formedness.  Every `MachineEvent.check` marker is observationally a
no-op.  The semantic terminal, frontier equality, typed two-tree
authentication, batched residual, relation boundaries, and final dot product
must therefore enter through a proved source-to-model theorem, not through a
trusted-tool assumption and not through a compiler-cover premise.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SourceAcceptanceBoundary

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement

/-! ## Strongest projection currently proved by `checkedRefine` -/

/-- This is the complete unconditional projection of checked deterministic
refinement currently available in the main Lean project. -/
theorem checked_refinement_exposes_replay_and_decoder_wellformedness
    (table : FixedOracleTable) (decoders : DeterministicDecoders)
    (tape : DeployedFixedTape) (raw : InteractiveRawTrace)
    (success : checkedRefine table decoders tape = some raw) :
    refine table tape = some raw ∧
      TraceWellFormed table decoders tape raw := by
  exact checked_refinement_is_well_formed table decoders tape raw success

/-! ## Checkpoint markers do not evaluate their named predicates -/

@[simp] theorem deterministic_checkpoint_marker_is_noop
    (table : FixedOracleTable) (state : EvalState) (checkpoint : Checkpoint) :
    runMachineEvent table state (.check checkpoint) = some state := by
  rfl

@[simp] theorem work_erased_checkpoint_marker_is_noop
    (table : FixedOracleTable) (state : EvalState) (checkpoint : Checkpoint) :
    runMachineEventWorkErased table state (.check checkpoint) = some state := by
  rfl

theorem terminal_and_merkle_checkpoint_markers_are_noops
    (table : FixedOracleTable) (state : EvalState) :
    runMachineEvent table state (.check .semanticTerminal) = some state ∧
      runMachineEvent table state (.check .frontierCount) = some state ∧
      runMachineEvent table state (.check .twoTreeAuthentication) = some state ∧
      runMachineEvent table state (.check .relationTerminal) = some state := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Exact acceptance remainder outside hash replay -/

/-- The three stage-local work predicates are evaluated by
`runGrindingChoice` before the corresponding marker.  They remain separated
here because no amount of grinding is a denominator in the knowledge bound. -/
def ThreeWorkAcceptanceFacts
    {frontierNodes : QuerySchedule → Nat}
    {Residual : Type*} {evaluateAt : Residual → Qm31Bytes → Qm31Bytes}
    {zero : Qm31Bytes} {messages : Messages}
    (facts : AcceptanceFacts frontierNodes Residual evaluateAt zero messages) :
    Prop :=
  facts.batchWork35Accepted ∧
    facts.foldWork31Accepted ∧
    facts.finalWork34Accepted

/-- Acceptance conditions not evaluated by the deterministic transcript
replay.  The typed `FirstCap203Search` itself is already carried by
`facts.querySearch`; this predicate contains the remaining parser, semantic,
frontier, Merkle/query, and terminal algebra. -/
def SourceAcceptanceRemainder
    {frontierNodes : QuerySchedule → Nat}
    {Residual : Type*} {evaluateAt : Residual → Qm31Bytes → Qm31Bytes}
    {zero : Qm31Bytes} {messages : Messages}
    (facts : AcceptanceFacts frontierNodes Residual evaluateAt zero messages) :
    Prop :=
  facts.canonicalFixedAndOpeningLimbs ∧
    facts.exactSemanticTerminal ∧
    facts.instructionFrontierMatches ∧
    facts.bothTypedTreesAuthenticate ∧
    facts.residualDegreeAtMost15 ∧
    BatchedQueryResidualZero Residual evaluateAt zero facts.residual
      (messages.challengeValue .queryBatch) ∧
    facts.allFourRelationBoundaries ∧
    facts.finalDotProductTerminal

/-- The deployed acceptance predicate is exactly the three work facts plus
the source acceptance remainder.  This is only logical reassociation of the
existing exact `Accepts` definition. -/
theorem accepts_iff_three_work_and_source_remainder
    {frontierNodes : QuerySchedule → Nat}
    {Residual : Type*} {evaluateAt : Residual → Qm31Bytes → Qm31Bytes}
    {zero : Qm31Bytes} {messages : Messages}
    (facts : AcceptanceFacts frontierNodes Residual evaluateAt zero messages) :
    Accepts facts ↔
      ThreeWorkAcceptanceFacts facts ∧ SourceAcceptanceRemainder facts := by
  constructor
  · intro accepted
    rcases accepted with
      ⟨canonical, semantic, batch, fold, finalWork, frontier, trees,
        degree, residual, relations, terminal⟩
    exact ⟨⟨batch, fold, finalWork⟩,
      ⟨canonical, semantic, frontier, trees, degree, residual, relations,
        terminal⟩⟩
  · rintro ⟨⟨batch, fold, finalWork⟩,
      ⟨canonical, semantic, frontier, trees, degree, residual, relations,
        terminal⟩⟩
    exact ⟨canonical, semantic, batch, fold, finalWork, frontier, trees,
      degree, residual, relations, terminal⟩

/-! ## `checkedRefine` alone cannot determine source acceptance -/

/-- For every checked-refinement success, the same tape/search can be placed
in an `AcceptanceFacts` record whose unmodeled terminal/Merkle facts are
false.  This does not refute the deployed verifier; it proves that the type of
`checkedRefine` success alone contains no theorem establishing those facts. -/
theorem checked_refinement_success_does_not_determine_acceptance_remainder
    (table : FixedOracleTable) (decoders : DeterministicDecoders)
    (tape : DeployedFixedTape) (raw : InteractiveRawTrace)
    (success : checkedRefine table decoders tape = some raw)
    (Residual : Type*) (evaluateAt : Residual → Qm31Bytes → Qm31Bytes)
    (zero : Qm31Bytes) (residual : Residual) :
    ∃ facts : AcceptanceFacts tape.frontierNodes Residual evaluateAt zero
        tape.messages,
      facts.querySearch = tape.search ∧
        ¬ SourceAcceptanceRemainder facts ∧
        ¬ Accepts facts := by
  have _operational :=
    checked_refinement_exposes_replay_and_decoder_wellformedness table decoders
      tape raw success
  let facts : AcceptanceFacts tape.frontierNodes Residual evaluateAt zero
      tape.messages :=
    { canonicalFixedAndOpeningLimbs := False
      exactSemanticTerminal := False
      batchWork35Accepted := True
      foldWork31Accepted := True
      finalWork34Accepted := True
      querySearch := tape.search
      instructionFrontierMatches := False
      bothTypedTreesAuthenticate := False
      residual := residual
      residualDegreeAtMost15 := False
      allFourRelationBoundaries := False
      finalDotProductTerminal := False }
  refine ⟨facts, rfl, ?_, ?_⟩
  · simp [SourceAcceptanceRemainder, facts]
  · simp [Accepts, facts]

/-!
The smallest source-to-model theorem still required is therefore a theorem
about the successful body of the opaque deployed transcript/relation call.
For the exact Rust inputs and returned transcript it must construct the
`FixedOracleTable`, `DeployedFixedTape`, decoder instantiation and raw trace;
prove `checkedRefine table decoders tape = some raw`; and prove
`SourceAcceptanceRemainder` for the corresponding `AcceptanceFacts`.

That theorem must derive, rather than assume:

* canonical proof parsing and the exact fixed/opening byte projection;
* program, release, statement-digest and attempt/proof-account bindings;
* the semantic terminal callback result;
* the instruction/frontier equality and first-cap-203 selected schedule;
* both typed 208-bit C1/C2 Merkle authentications with shared topology;
* the degree-at-most-15 rho-batched residual equality;
* all four relation boundaries and the final four-value dot product.

Separately, the transaction wrapper must supply tag 73, exact instruction
length, finalized proof-account bounds, compiled release binding,
`attempt_id = proof_account.key`, statement-digest recomputation and
`check_pow = true`.  Those are outside the extracted read-only root.  The only
permitted trusted statement is that pinned Charon/Aeneas faithfully translate
the Rust functions they actually translate; opacity of a callee is not a
translation-correctness proof of that callee.
-/

#print axioms checked_refinement_exposes_replay_and_decoder_wellformedness
#print axioms deterministic_checkpoint_marker_is_noop
#print axioms work_erased_checkpoint_marker_is_noop
#print axioms terminal_and_merkle_checkpoint_markers_are_noops
#print axioms accepts_iff_three_work_and_source_remainder
#print axioms checked_refinement_success_does_not_determine_acceptance_remainder

end AspisK1.V7Tag73SourceAcceptanceBoundary
