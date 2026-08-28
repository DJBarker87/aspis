# V7 persistent transcript-role audit — 2026-08-28

## Result

The operational oracle admits a conservative executable role instrumentation,
and prepared restoration forks retain enough pre-answer information to recover
their exact squeeze owner and block as ghost data.  This does not close the
unconditional K1.5 actual-law bound: an arbitrary root adversary query can
choose, after seeing its answer, whether that query is used by the eventually
returned proof.  The current pre-answer state does not distinguish those
continuations, and a completed-proof lookup cannot be used to label the older
coordinate retroactively.

No protocol, transcript byte, proof byte, challenge sampler, verifier result,
CU behavior, or cryptographic assumption was changed.

## Why retrospective cache provenance is insufficient

`source_aware_cached_record_master_tape_or_programmed` proves that a cached
answer is either an earlier compiler-tape answer or an earlier programmed
answer.  It deliberately does not assign a semantic role to that earlier
coordinate.  Selecting the earlier record after inspecting the accepted proof
would make the coordinate and its bad set depend on future execution.

The guarded persistent tracker therefore refuses to install a role when the
input already occurs in the oracle table.  A cached unbound input stays
unbound.  This makes the remaining gap visible instead of converting a
post-run provenance witness into a purported pre-answer coordinate.

## Why `rawCalls = verifierHistory` remains false

`InteractiveRawTrace.calls` contains adversary grinding probes before each
selected work nonce.  `RawVerifierExecution.verifierHistory` is the later
verifier-only projection and intentionally removes those probes.  The
regression guards remain:

- `exact_operational_verifier_history_eq_canonical_pairs`;
- `exact_operational_verifier_history_eq_raw_calls_iff`;
- `run_grinding_choice_work_erased_calls_length`.

The role instrumentation does not redefine either trace.

## Automaton state and assignment rule

The generic state is:

```lean
PersistentRoleMachineState Control Role
```

It contains the existing `OracleState`, an executable policy control state,
and an ordered persistent map from exact `ShaInput` values to roles.  The
policy interface is data-only:

```lean
ExecutablePreAnswerRolePolicy Control Role
```

Its `classify` function receives control, actor, the pre-query oracle state,
and the current input, but not the current answer.  `afterQuery` and
`afterProgramming` may use a completed operation only to update control for
future inputs.

Before an operation, a role is installed only if all three checks succeed:

1. the role has not been used;
2. the input has not been bound;
3. `lookupEntry oracle input = none`.

Consequently the assignment is made before a first fresh/programmed exposure.
Cached inputs cannot acquire a role retrospectively, unrelated calls cannot
delete bindings, and first binding wins.

## Erasure and cache provenance

The principal erasure theorems are:

- `query_oracle_with_executable_roles_erases`;
- `program_oracle_with_executable_roles_erases`;
- `query_oracle_with_preanswer_roles_erases`;
- `program_oracle_with_preanswer_roles_erases`.

They erase definitionally to the existing `queryOracle` and `programOracle`.
Thus query order, answers, table lookup, cache behavior, programming history,
and abort behavior are unchanged.

The principal persistence facts are:

- `guarded_install_success_binds_exact_input`;
- `prepare_existing_input_preserves_roles`;
- `cached_reuse_observation_was_previously_bound`;
- `cached_unbound_query_remains_unbound`.

For restoration, `ready_preparation_has_pair_role` derives the exact
`SqueezeOwner`, block, output input, and advance input from the already-selected
`FutureFreeTransition` before either fork answer is sampled.
`prepared_pair_role_erases_to_fork_header` and
`dispatch_prepared_restoration_emits_role_erased_fork` prove conservativity
with the current scheduler fork.

## Exact boundary by execution source

### Root verifier fresh exposure

The role is pre-answer data.  Existing classifiers cover semantic sequential,
relation-alpha, and q16 calls from verifier history/control.  Gamma needs the
analogous variable-prefix history automaton, but its role is observable in
principle.

### Prepared restoration fork

The role is pre-answer data in `PreparedConcreteRestoration.transition`.  The
new ghost projection recovers it without changing `forkPair`.  The current
erased scheduler request retains the two inputs but not owner/block, so a
future integrated router must consume the ghost projection at preparation
time.

### Root adversary fresh exposure

The exact eventually-retained role is not determined by history and input.
`same_preanswer_query_has_distinct_eventual_dispositions` constructs two
executions of the same query node and continuation, differing only in the
fresh answer, whose eventual dispositions differ.  Therefore a generic
history/input-only classifier cannot label the coordinate as retained versus
erased for both runs.

The residual continuation is available pre-answer and can define an
answer-indexed counterfactual strategy, but the current model has no theorem
that discovers which arbitrary adversary query will be selected by the final
proof without inspecting that future proof.

## Event-family status

The following mathematical endpoints remain valid and unchanged:

- copy-lambda;
- copy-chi;
- mu-zero;
- inactive-chi;
- OOD mix;
- guarded kappa;
- semantic sequential family;
- relation-alpha rounds 0–3;
- exact variable-prefix gamma;
- q16 decoder-prefix and finite-cardinality machinery.

They are genuinely prechallenge on root verifier-fresh coordinates and on
role-retaining prepared restoration coordinates.  They are not yet proved
prechallenge for an accepted verifier cache hit whose first fresh creation was
an arbitrary adversary query.

## K1.3 and K1.4 reuse

For K1.3, use role `Q16DigestSlot = Fin 64 × Fin 8` and the existing
`schedulerHistoryQ16Label`, `exactPlainRomHistoryQ16Coordinates`, and decoder
prefix lemmas.  The missing common step is the first-source compatibility and
prefix-freeze theorem: the size-9557 bad set must depend only on the residual
pre-q16 state.

For K1.4, use a 24-slot variable-prefix gamma role (`Fin 12 × Fin 2`) and the
existing variable-prefix probability bridge.  The response provider must be a
function only of the frozen pre-gamma state and residual tape.  Actual replay
equality still depends independently on parsed-proof source binding.

## K1.5 and K1.6 outcome

The following actual-law obligations remain open:

```lean
FixedK15EventBounds
  (exactCompilerJointLaw hiddenLaw parameters)
  (exactTag73RestoredFixedK15Events environment)
```

and:

```lean
(exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
    (exactTag73RestoredK15ResidualEvent environment) ≤
  exactK14IdealRawError
```

No new probability premise was added.  Consequently the K1.5 premise remains
in the corrected K1.6 capstone.  The exact raw K1.5 value remains:

```text
336869027002169 / (P^4 - 1)
```

with no grinding normalization or independence assumption.

## Remaining source/Aeneas obligations

The current-revision source bridge still needs at least:

```lean
∃ decoded : Fin 641 → QM31Exact,
  FixedFieldDecodeExact (fixedTapeRawMessages fixed.base.tape) decoded
```

plus wire-opening projection and the current-revision equality connecting
Rust transcript/parser results to the derived K1.3 view.  Rust does not expose
a pre-answer role trace or total Lean `ExactSchedule`; the canonical schedule
is constructed mathematically instead.  The stale translated Aeneas bundle is
not imported.

If a source trace is added, its minimal ghost output is the existing
`RawQueryRole` (owner, block, output/advance half), before-state digest, exact
input/output, and sampler stop/decode decision for every hash callback.  q16
also needs candidate counter/block and selected schedule.  This is a
source/Aeneas observation theorem, not a wire or protocol change.

## Blocker classification

- Semantic-model deficiency: arbitrary-adversary selected-role discovery and
  loss of restoration owner/block at scheduler erasure.
- Source/Aeneas deficiency: current fixed-field/parser/wire equality and role
  trace are absent.
- Probability-mathematics deficiency: none identified in the retained K1.5
  numerator/cardinality/sampler results.
- Genuine protocol limitation: none established; the arbitrary-adversary
  selection issue needs either a stronger counterfactual discovery theorem or
  an explicitly accounted adaptive-query loss, not an assumed role label.
