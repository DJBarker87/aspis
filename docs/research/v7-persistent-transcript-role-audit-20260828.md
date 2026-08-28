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

Inspection of the current Rust answers the implementation fork positively for
every production-controlled call: the control site knows the challenge kind,
round/attempt/block, transcript state, and query bytes before invoking the
hash callback.  No Rust scheduler refactor is needed.  This positive result
does not cover a coordinate first exposed by the arbitrary adversary before
the verifier reaches that control site.

No protocol, transcript byte, proof byte, challenge sampler, verifier result,
CU behavior, or cryptographic assumption was changed.

## Current Rust pre-answer ordering audit

The current production source fixes the role before the answer at these call
sites:

- lambda and chi in `v6_transcript.rs` immediately after C1 absorption;
- theta, zerocheck coordinates 0--9, and mu in
  `state_only_sumcheck.rs::begin_state_only_zerocheck`;
- eta in `state_only_hiding.rs::begin_state_only_masked_sumcheck`;
- semantic round challenges inside the round-indexed loop in
  `verify_compact_semantic_sumcheck`;
- gamma, kappa, both secure-circle points, and both OOD mixes in
  `finish_onefold_relation`;
- relation alpha 0 before the final-256 boundary and alpha 1--3 in the
  explicit relation-round loop;
- q16 candidate counter and decoder block in
  `v7_onefold.rs::derive_first_v7_compact_queries`;
- the query-batch challenge after the accepted q16 branch is installed.

For a variable-prefix sampler, each attempt/block has a pre-answer role.  The
post-answer fact is only whether that attempt stops the sampler.  Likewise a
q16 candidate is labelled by `(counter, block)` before decoding; `selected`
and `frontier_nodes` are deliberately not pre-answer labels.

`verifierActionPreAnswerRoles` is the executable Lean projection of this
control boundary.  Its theorem
`verifier_action_preanswer_roles_inputs_exact` proves that erasing the roles
is exactly `verifierIssuedInputs`; historical grinding evidence maps to the
empty verifier-query list.  The existing verifier program is consequently
proved to query those same inputs by
`verifier_action_program_uses_preanswer_role_inputs`.

The audited current source identities are:

```text
transcript.rs                 be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119
state_only_sumcheck.rs        5458d3134a3123b8b02bef0374ccbf96a05461974d7e274966c6a3f0d2d496f9
state_only_hiding.rs          38cb7244635968d331c056ab3eaf468c5a377c4d7efc97855083293b9f2de39a
v6_transcript.rs              f866e94e3b22ce3ab2c636423dfb9191fb1dd30f452b9134a02044b109a85f2d
v7_onefold.rs                 c89c85c7027b63bac93d4ca07284ee336b6a78a0428831287a93593c629e0dff
v6_onefold.rs                 8a97d99aa4c49293cdada6edd9caf07fec602d5a996b655b18272e4485739438
v6_onefold_prover.rs          6b394c31bc55da32fd116a90c159a897160a99d5d4843cd5b7ee05e9876a850d
programs/.../v7_verifier.rs   4de89a2d0f01b2463fb0fad9112234ddded774ffe27cb5c4e8c7d478275c3200
```

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

The semantic cache view adds:

- `persistent_role_cache_erases`;
- `lookup_persistent_role_cache_erases`;
- `successful_cached_query_preserves_persistent_role_cache`;
- `successful_cached_query_reads_original_tagged_entry`;
- `successful_fresh_query_appends_preanswer_tagged_entry`;
- `successful_program_appends_preanswer_tagged_entry`;
- `tagged_exact_fixed_root_records_erase`.

Thus a later cache hit inherits the tag and `TableSource` of the original
fresh/programmed installation, while erasure is exactly `OracleState.table`
and `exactFixedRootRecords`.

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

The role is pre-answer data, and the exact action/input projection is now
proved in Lean.  Existing classifiers cover semantic sequential,
relation-alpha, q16, and the exact variable-prefix gamma calls from
verifier history/control.  A current-revision Aeneas replay connecting the
Rust call sites to this action projection is still absent.

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

The current fixed-field reader consumes exactly 641 QM31 values and
`finish_onefold_relation` calls `fields.finish()` before returning.  The new
bridge reduces the required current-source theorem to the coordinatewise
reader projection:

```lean
∃ decoded : Fin 641 → QM31Exact,
  CurrentSourceFixedFieldProjection
    fixed.base.runtime.adversaryValue.rawMessages decoded
```

`current_source_fixed_field_projection_iff_decode` proves this is exactly
equivalent to `FixedFieldDecodeExact`, and
`fixed_clean_root_has_exact_fixed_field_decode_of_current_source` transports
it through the existing raw-message equality.  This is a minimized source
obligation, not a theorem currently supplied by Aeneas.

The remaining parsed-wire equality is exactly:

```lean
ExactOperationalParsedWireProjection input decoded
```

meaning:

```lean
exactK13ParsedProof input =
  derivedK13View input decoded (exactK13ParsedProof input).openings
```

That equality constructs `ExactParsedProofSourceBinding`; its inverse-table
field is already discharged by the canonical schedule theorem.  Preferably,
downstream classifiers should consume `derivedK13View` directly, removing
this legacy opaque-`rawProof` equality.

The archived accepted-source bundle predates the current transcript/parser
implementation and leaves the transcript/relation call opaque.  The 20260827
K1.3 bundle is pinned to `b44fc616` and covers the batch helper, not q16 or the
packed reader.  Neither is imported as a current-source proof.  A new
current-revision extraction must cover the sampler methods, transcript prefix
helpers, semantic/relation loops, q16 scheduler, deferred parser,
`V6FixedFieldReader::{new,next_qm31,finish}`, and the V7 verifier entrypoint.

If a source trace is added, its minimal ghost output is the existing
`RawQueryRole` (owner, block, output/advance half), before-state digest, exact
input/output, and sampler stop/decode decision for every hash callback.  q16
also needs candidate counter/block and selected schedule.  This is a
source/Aeneas observation theorem, not a wire or protocol change.

## Blocker classification

- Semantic-model deficiency: arbitrary-adversary selected-role discovery.
  Prepared restoration owner/block is recoverable by the ghost projection,
  but the erased scheduler still does not carry it directly.
- Source/Aeneas deficiency: the current fixed-field/parser/wire equality and
  the current Rust-to-`VerifierAction` pre-answer role trace are absent.
- Probability-mathematics deficiency: none identified in the retained K1.5
  numerator/cardinality/sampler results.
- Genuine protocol limitation: none established; the arbitrary-adversary
  selection issue needs either a stronger counterfactual discovery theorem or
  an explicitly accounted adaptive-query loss, not an assumed role label.

## Focused verification

All timings use `/usr/bin/time -l`; swap was zero for every build.

| Target | Wall | Peak RSS |
| --- | ---: | ---: |
| `V7Tag73VerifierActionPreAnswerRoles` | 5.75 s | 5,665,734,656 bytes |
| `V7Tag73PersistentRoleCacheErasure` | 2.57 s | 798,556,160 bytes |
| `V7Tag73CurrentSourceDecodeBridge` | 2.63 s | 800,030,720 bytes |
| `V7Tag73PersistentTranscriptRoleReplay` | 5.46 s | 5,664,931,840 bytes |

The replay prints axioms for every principal theorem.  The complete union is
`propext`, `Classical.choice`, and `Quot.sound`.  The forbidden-construct scan
and `git diff --check` are clean.
