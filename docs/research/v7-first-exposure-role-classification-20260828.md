# V7 first-exposure role classification — 2026-08-28

## Classification: D — genuine adversarial prequery event required

There is no answer-independent classifier from the deployed raw SHA
coordinate to the full Tag-73 verifier role.  There is also no such classifier
from an otherwise unrestricted `OracleState.history` and current input: the
same history/input pair can be followed by distinct logical verifier actions.

The current Rust result remains positive but narrower.  At every
verifier-origin call site, the control frame fixes the challenge kind,
attempt/counter/block and output/advance half before the hash result is
consumed.  That proves the role of a call issued by the verifier.  It does not
give an earlier arbitrary adversary call a verifier control frame, and it does
not retroactively tag an already-cached coordinate.

The exact classification is therefore D, not C: current Rust does not rule
out an arbitrary adversary querying a future verifier coordinate.  The
remaining reduction must distinguish a canonically classifiable transcript
prequery from a genuinely unreserved prequery and charge the latter at the
existing causal compiler boundary.  No new K1.5 probability term has been
introduced.

The kernel witnesses are in
`V7Tag73FirstExposureRoleClassification.lean`:

- `squeeze_output_coordinate_forgets_owner_and_block`;
- `squeeze_advance_coordinate_forgets_owner_and_block`;
- `no_raw_coordinate_classifier_classifies_lambda_and_gamma`;
- `no_history_input_classifier_classifies_lambda_and_gamma`;
- `same_preanswer_coordinate_can_have_distinct_future_roles`;
- `prior_output_coordinate_for_later_fresh_state_hits_target`;
- `prior_advance_coordinate_for_later_fresh_state_hits_target`;
- the two `target_clean_fresh_state_was_not_prequeried_*` theorems.

The counterexample is deliberately scoped to the arbitrary oracle/action
abstraction.  It constructs an actual fresh adversary `queryOracle` call and
an actual later verifier cache hit.  At one fixed `RuntimeCore`, lambda and
gamma have distinct `RawQueryRole`s but definitionally identical issued SHA
inputs.  It does not claim two complete accepted Rust transcripts with the
same state; proving or excluding those requires the missing canonical
transcript-lineage bridge described below.

## Exact representation inventory

Every challenge sampler block uses two calls:

```text
output  = SHA256(beforeDigest || 0x01)
advance = SHA256(beforeDigest || 0x02)
```

`RawQueryRole` retains the owner and block as semantic metadata.  Its `input`
function erases both.  The output and advance grammars are structurally
disjoint, and equality within one half implies equality of `beforeDigest`.
Neither fact recovers the owner or block.

| Consumed family | Lean owner / role | Pre-answer control data | Exact raw sampler input | Role/domain label in those bytes? | Can another role have identical bytes? | Can the adversary issue it first? | Strongest honest classifier now |
|---|---|---|---|---|---|---|---|
| copy lambda | `.challenge .lambda`, block | verifier phase, ordinary sampler block | `S || 0x01`, `S || 0x02` | half only | yes, every owner at the same `S` and half | yes | verifier action/control only |
| copy chi | `.challenge .chi`, block | phase after lambda, ordinary block | same grammar | half only | yes | yes | verifier action/control only |
| mu-zero | `.challenge .mu`, block | zerocheck loop completion, ordinary block | same grammar | half only | yes | yes | verifier action/control only |
| inactive chi | `.challenge .chi`, block | same chi site; event meaning is later algebra | same grammar | half only | yes | yes | verifier action/control only |
| semantic theta | `.challenge .theta`, block | helper-sum absorb marker | same grammar | half only | yes | yes | verifier history parser at verifier calls |
| zerocheck positions | `.challenge (.zerocheckPoint i)`, block | fixed loop position `i : Fin 10` | same grammar | half only | yes | yes | verifier history/control |
| eta | `.challenge .eta`, block | masked-claim absorb | same grammar | half only | yes | yes | verifier history/control |
| semantic rounds | `.challenge (.semantic r)`, block | round absorb and `r : Fin 10` | same grammar | half only | yes | yes | `semanticHistoryPhase` on verifier history |
| OOD mix | `.challenge (.oodMix sample)`, block | circle sample loop `sample : Fin 2` after value absorb | same grammar | half only | yes | yes | verifier action/control |
| guarded kappa | `.challenge .kappa`, block | inactive-claim absorb, nonzero attempt/block | same grammar | half only | yes | yes | verifier action/control |
| circle point | `.challenge (.circlePoint sample)`, block | circle sample loop and candidate block | same grammar | half only | yes | yes | verifier action/control |
| gamma / variable prefix | `.challenge .gamma`, block | post-batch-work state, nonzero attempt/block | same grammar | half only | yes | yes | verifier action/control; stopping is post-answer |
| relation alpha 0 | `.challenge (.alpha 0)`, block | round-zero polynomial and fold-work absorbs | same grammar | half only | yes | yes | `relationAlphaHistoryPhase 0` on verifier history |
| relation alpha 1/2/3 | `.challenge (.alpha r)`, block | relation-round absorb and `r : Fin 4` | same grammar | half only | yes | yes | four verifier-history routers |
| q16 candidate | `.queryCandidate counter`, block | cloned transcript, candidate absorb, `counter : Fin 64`, decoder block | same grammar | half only; counter is in the preceding absorb, not this input | yes, all counters/blocks/owners at the same `S` | yes | `schedulerHistoryQ16Label` at verifier requests |
| query batch | `.challenge .queryBatch`, block | accepted q16 branch plus query-batch absorb | same grammar | half only | yes | yes | verifier action/control |

For all rows, the complete production control state contains more than the
raw coordinate.  It contains the exact call site, loop index, sampler mode,
and current transcript state.  `verifierActionPreAnswerRoles` is the Lean
projection of precisely that information, and
`verifier_action_preanswer_roles_inputs_exact` proves that erasing it gives
`verifierIssuedInputs`.

The q16 counter is worth separating from the sampler call.  Rust first
absorbs `V7_QUERY_CANDIDATE || counter`, then calls the unlabelled duplex
sampler.  Thus the resulting digest cryptographically binds the counter, but
the following 33-byte query does not syntactically expose it.  The same is
true of semantic/relation round markers: they occur in earlier absorbs, not
in the squeeze input itself.

## Current Rust audit

`Transcript::squeeze_block` in `crates/aspis-core/src/transcript.rs` constructs
only `[state; 32] || DOM_SQUEEZE`, then changes the final byte to
`DOM_ADVANCE`.  No owner, phase, attempt, counter, block, or challenge ID is
hashed.

The role is nevertheless fixed at each production call site before the
result:

- lambda and chi in `v6_transcript.rs`;
- theta, zerocheck coordinates and mu in `state_only_sumcheck.rs`;
- eta in `state_only_hiding.rs`;
- semantic rounds in `verify_compact_semantic_sumcheck`;
- gamma, kappa, circle points, OOD mixes and relation alphas in
  `finish_onefold_relation`;
- q16 counter candidates in `v7_onefold.rs::derive_first_v7_compact_queries`;
- query-batch rho after the accepted q16 transcript is installed.

For a variable-prefix sampler, the candidate block role is pre-answer; only
accept/retry is answer-dependent.  For q16, `(counter, block)` is pre-answer;
selected counter and frontier size are post-answer and are correctly absent
from the causal role.

No scheduler refactor is needed for verifier-origin calls.  A refactor at
those sites would not solve the adversary-first case because the earlier
caller is the arbitrary adversary, not the verifier.

## Uniqueness and collisions

The structural disjointness boundary is exact:

- `S || 0x01` never equals `T || 0x02`;
- equality of two output coordinates implies `S = T`;
- equality of two advance coordinates implies `S = T`;
- owner and block are erased even when `S` is fixed.

Consequently role uniqueness cannot be obtained by ordinary byte parsing.
It must come from a canonical transcript lineage leading to `S`.  Different
role lineages reaching the same `S` are not syntactically impossible; ruling
them out belongs at the full-256 collision/forward-reference boundary, not at
a fake role-tag parser.

`lambda_and_gamma_actions_have_identical_inputs_at_same_core` and
`gamma_and_q16_actions_have_identical_inputs_at_same_core` are exact examples.
`same_owner_distinct_blocks_are_distinct_roles` shows that even block number
cannot be recovered from one same-state coordinate.

## Exact adversary-first test

`same_preanswer_coordinate_can_have_distinct_future_roles` uses a two-call,
one-fresh oracle budget:

1. the adversary queries `S || 0x01`; the controller supplies `y`, installing
   a fresh table entry;
2. the verifier queries the same input and receives `y` from cache;
3. at the same `RuntimeCore`, both lambda and gamma action plans issue that
   same input, although their `RawQueryRole`s are unequal.

Therefore a cache hit cannot acquire lambda or gamma retrospectively.  The
persistent cache theorems correctly preserve the original tag (or absence of
a tag).

The generic regression theorem
`same_preanswer_query_has_distinct_eventual_dispositions` also remains.  The
new Tag-73-specific witness does not invalidate or redefine it.

## The already-covered future-state prequery case

Suppose a record for `S || 0x01` or `S || 0x02` is already in the operational
history when a later fresh coordinate returns the digest `S`.  The earlier
record literally contains `S` as its first 32 bytes.  The new theorems prove
that `S` is therefore a member of:

```lean
operationalRequestTargets seen state.history currentInput
```

At a target-clean exposure this is impossible.  At sample level, failure of
the operational certificate is the existing event:

```lean
exactForwardReferenceOrProgrammingConflictEvent transitionFuel configuration
```

and
`exact_forward_reference_or_programming_conflict_event_subset_target` proves
that it is a subset of `exactPlainRomTargetEvent`.  The actual-law target
probability is already bounded by
`exact_compiler_target_probability_le_div_two_pow_256`.  It is charged once
in the compiler accounting, not added to the K1.5 numerator.

This settles only “the adversary named the state before the state was
sampled.”  It does not settle an adversary query made after `S` is already a
known output but before the eventual verifier role has been canonically
identified.

## Minimal remaining causal interface

The missing result is not another probability-shaped K1.5 premise.  It is a
trace partition for every accepted verifier cache hit whose original table
installation was adversary-origin:

```lean
-- Required theorem shape; intentionally not declared as an assumption.
theorem adversary_first_cached_verifier_use_partition
    (sample : ExactCompilerSample HiddenTape parameters)
    (later : AcceptedVerifierCachedRoleUse
      transitionFuel configuration projection sample) :
    sample ∈ exactPlainRomTargetEvent transitionFuel configuration ∨
      ∃ original : OriginalFreshOrProgrammedExposure sample later.input,
        original.occursBeforeAnswer ∧
        canonicalTag73RoleFromPrefix?
            original.preAnswerCursor original.input = some later.role
```

Here `AcceptedVerifierCachedRoleUse`,
`OriginalFreshOrProgrammedExposure`, and the canonical prefix parser do not
yet exist as one current-source-backed interface; the displayed statement is
the exact shape still needed, not an axiom added to Lean.

The classifier in the right branch must be executable from the original
pre-answer cursor.  It may traverse already-existing absorb/squeeze lineage,
ignore unrelated adversary calls, and use source-visible transcript phase and
counter markers.  It may not inspect the fresh answer, completed proof,
future verifier action, acceptance, or the later cache-hit tag.

The corresponding causal bad event can only be the left branch if it is rare.
The future-state subcase is included in the existing target event.  The
known-state subcase is different: after `S` is public, an adversary can query
`S || domain` deliberately, so occurrence of that query can have probability
one.  It cannot honestly be assigned a small prequery numerator.  The
remaining reduction must instead fork/replay from that original occurrence
and construct the whole response family, or expose a source/model restriction
that rules the execution out.  The current arbitrary-adversary model supplies
no such restriction.

## Existing routers and why they are not yet the missing classifier

- `semanticHistoryPhase` and `relationAlphaHistoryPhase` deliberately scan
  verifier records and ignore non-verifier actors.
- `schedulerHistoryQ16Label` labels a selected verifier fresh request.
- `verifierActionPreAnswerRoles` labels a verifier action already reached.
- the persistent cache stores a role chosen at first exposure, but correctly
  refuses to relabel an existing unbound entry.

These are all valid.  None selects, before an arbitrary adversary answer, the
unique canonical Tag-73 transcript lineage among interleaved adversary calls.
Extending them by reading the completed proof would be anticipatory.

This limitation is now kernel-checked directly by:

- `scheduler_semantic_label_of_adversary_fresh_is_none`;
- `scheduler_relation_alpha_label_of_adversary_fresh_is_none`;
- `scheduler_q16_label_of_adversary_fresh_is_none`;
- `existing_verifier_origin_routers_do_not_label_adversary_first_exposure`;
- `adversary_first_then_verifier_cached_has_one_fresh_answer`.

The last theorem records that the adversary creates the sole fresh answer and
the later verifier record is cached.  A fresh-exposure router therefore has no
later coordinate on which it can repair the missing label.

The smallest honest semantic addition is therefore not a stronger raw-input
classifier.  It is an open, stepwise adversary/prover continuation interface
from the original occurrence, sufficient for the restoration compiler to run
every counterfactual answer and recompute all later verifier challenges.  The
repository already contains the intended executable shape:

```lean
inductive OpenTag73TailProgram (Result : Type*) where
  | returned (result : Result)
  | rejected
  | step (action : VerifierAction)
      (next : VerifierReply -> OpenTag73TailProgram Result)

structure OpenTag73TailBlackBox
    (HiddenTape Observation Result : Type*) where
  start : HiddenTape -> Observation -> OpenTag73TailProgram Result
```

What is missing is a current-source/semantic erasure theorem connecting such
an open program to the production arbitrary adversary and then to each
restoration child.  `SameTapeBlackBox` exposes only a final parsed proof.
`same_hidden_tape_return_can_change_an_earlier_field` proves why a returned
whole proof cannot be reused as the required post-checkpoint continuation.
This interface should be shared by K1.3 q16, K1.4 width-29 and K1.5; three
bespoke post-hoc routers would not solve the causal issue.

This refines the classification to **D: a causal adversarial-prequery replay
is required**, with a **semantic-model deficiency** as the immediate blocker.
The prequery's mere occurrence is not a sound small-probability event.  No
protocol limitation has been established, and the audited Rust verifier call
sites still fix their own roles before consuming answers.

## Source/Aeneas boundary

The current-source obligations remain separate:

```lean
∃ decoded : Fin 641 → QM31Exact,
  CurrentSourceFixedFieldProjection
    fixed.base.runtime.adversaryValue.rawMessages decoded
```

and:

```lean
ExactOperationalParsedWireProjection input decoded
```

The established bridges are:

- `current_source_fixed_field_projection_iff_decode`;
- `fixed_clean_root_has_exact_fixed_field_decode_of_current_source`;
- `exact_parsed_proof_source_binding_of_operational_projection`.

A fresh current-revision extraction must additionally connect the Rust
transcript call sequence to `VerifierAction`, including the before-digest,
owner, counter/block and output/advance half before the callback returns.
That source theorem proves verifier-origin role ordering.  The adversary-first
partition still requires the semantic transcript-lineage theorem; source
extraction alone cannot constrain an arbitrary adversary program.

No stale Aeneas bundle is imported.

## K1.3/K1.4/K1.5 consequence

The classification does not discharge either remaining K1.5 actual-law
premise:

```lean
FixedK15EventBounds
  (exactCompilerJointLaw hiddenLaw parameters)
  (exactTag73RestoredFixedK15Events environment)
```

```lean
(exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
    (exactTag73RestoredK15ResidualEvent environment) ≤
  exactK14IdealRawError
```

K1.3 q16 and K1.4 width-29 have the same adversary-first causal gap.  Their
sampler/cardinality mathematics and existing verifier-fresh routers remain
valid.

The K1.5 raw value is unchanged:

```text
336869027002169 / (P^4 - 1)
```

No grinding normalization, independence premise, or extra union bound was
introduced.  K1.6 retains its genuine K1.3/K1.4/K1.5 premises.

## Regression and change boundary

The result does not assert `rawCalls = verifierHistory`; grinding probes
remain present only in raw execution.  The guards
`exact_operational_verifier_history_eq_canonical_pairs`,
`exact_operational_verifier_history_eq_raw_calls_iff`, and
`run_grinding_choice_work_erased_calls_length` remain unchanged.

No Rust, protocol bytes, proof bytes, wire format, sampler behavior, verifier
semantics, CU behavior, or cryptographic assumption changed.

## Focused verification

The focused leaf and import replay are kernel-green:

```text
lake env lean AspisFormal/K1/V7Tag73FirstExposureRoleClassification.lean
  wall:     3.86 s
  peak RSS: 5,562,187,776 bytes
  swaps:    0

lake build AspisFormal.K1.V7Tag73FirstExposureRoleClassification \
           AspisFormal.K1.V7Tag73PersistentTranscriptRoleReplay
  wall:     9.24 s
  peak RSS: 5,717,655,552 bytes
  swaps:    0

lake env lean AspisFormal/K1/V7Tag73PersistentTranscriptRoleReplay.lean
  wall:     4.03 s
  peak RSS: 5,647,859,712 bytes
  swaps:    0

lake env lean AspisFormal/K1/V7Tag73AdversaryPrequeryRouterGap.lean
  wall:     4.06 s
  peak RSS: 5,641,207,808 bytes
  swaps:    0
```

The machine-wide swap allocation was already in use by other work
(`8,943.75 MiB` at the final replay); each measured focused command itself
reported zero swaps.  No memory-heavy NUC build was started.

The complete `#print axioms` union for the new terminal theorems and focused
replay is:

```text
propext
Classical.choice
Quot.sound
```

`git diff --check` and the focused forbidden-construct scans are clean.
