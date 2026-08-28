# V7 one-transaction formal/source consolidation

Date: 2026-08-28

## Frozen runtime candidate

The authoritative candidate is branch
`research/v7-one-tx-activate-20260828`, based on activation commit
`d0bfca5c6e7218caa25c261584bc0ca65ed80021`.

The complete eight-lane Pool path is measured in one transaction:

| Path | TxV1 bytes | CU |
| --- | ---: | ---: |
| transfer, same page | 799 | 1,145,890 |
| transfer, rollover | 832 | 1,191,463 |
| withdrawal, same page | 964 | 1,136,135 |
| withdrawal, rollover | 997 | 1,201,718 |

The selected verifier retains the exact Tag-73 transcript, 208-bit Merkle
profile, q16 schedule, work checks, relation and proof grammar. The CU changes
are evaluator identities: fixed semantic prefactorisation, sparse active-mask
basis, tensorized selectors, grouped Copy dot products, packed range residuals
and the gamma four-slot loop interchange.

## Selected evaluator source bridge

Commits `99fcfa2f` and `961e8e07` add the mathematical identity proof and the
source-schedule bridge. Commit `760d2473` refreshes the source manifest for the
aggregate activated feature without broadening the pinned source leaves.

The source pin replay passes on the activated branch. The focused Lean source
bridge passed on `nuc.local`:

```text
unit: aspis-v7-one-tx-formal-consolidation-03
result: PASS
wall: 2:52.30
maximum RSS: 6,949,060 KiB
swap: 0
axiom union: propext, Classical.choice, Quot.sound
```

The two mutating slice helpers which Aeneas cannot currently translate remain
represented by their clean Charon LLBC and universally quantified
source-shaped event functions. This is still a mechanical source-refinement
gate, not a mathematical or cryptographic assumption, and must remain visible
until direct translation or an equivalent caller theorem removes it.

## Literal Merkle caller to exact K1.2

Commit `9e3e29a1` integrates the literal translated production caller with the
maintained exact K1.2 model. The strongest theorem is:

```text
literal_production_callers_construct_exact_tag73_k12_source_obligations
```

It derives both exact K1.2 source obligations from successful translated
caller control flow. The only semantic input at this seam is per-call
SHA-callback reflection into the shared lazy-oracle history; it is the explicit
SHA/random-oracle runtime boundary, not an accepted-opening or coverage
premise.

The current consolidated source was compiled under both maintained Lean 4.32
and the Aeneas bundle's Lean 4.31 kernel. The exact integrated replay used the
matching Lean 4.31 object graph:

```text
unit: aspis-v7-one-tx-k12-exact-integration-02
invocation: bf628c710afd4d929416ad7e18ede37d
result: PASS
wall: 1:42.38
maximum RSS: 6,945,780 KiB
swap: 0
axiom union: propext, Classical.choice, Quot.sound
```

The preceding maintained Lean 4.32 target also passed in 10:18.44 with a
2.3 GiB cgroup peak and zero swap. A refreshed Lean 4.31 dependency target
passed in 4:50.05 with a 1.9 GiB cgroup peak and zero swap.

There is no `sorry`, `admit`, `sorryAx`, `native_decide`, project-specific
axiom or conclusion-shaped K1.2 premise in the compiled bridge.

## Activated Pool caller/writeback source bridge

Commit `f41507cb` supplies the translated operational caller theorem. The
strongest success and rejection endpoints are:

```text
translated_accepted_atomic_transaction_has_exact_writeback
translated_rejected_atomic_transaction_is_exact_prestate
```

The source audit now pins activation base `d0bfca5c`, the exact selected Pool
and verifier manifests, current caller/processor/verifier source hashes, active
direct-result path, six-account verifier CPI, borrow-before-CPI ordering and
the no-fallible-call-after-first-write tail. It passes on macOS and from the
exact synced Linux source copy.

The projected Rust replay passes all four transfer/withdrawal times
same-page/rollover paths and exact rollback cases. The Lean replay passed on
the NUC:

```text
unit: aspis-v7-one-tx-pool-caller-lean-01
invocation: f2fb324535194ccba3c43a84ebc61a33
result: PASS
wall: 21.28 seconds
maximum RSS: 2,640,900 KiB
swap: 0
axiom union: propext, Classical.choice, Quot.sound
```

The direct literal production caller to fixed-width operational projection is
still a named Charon/Aeneas/compiler-refinement seam. Exact current hashes and
control flow are pinned, but this is not yet presented as a theorem from the
full Solana `AccountInfo` implementation. It remains a release gate under the
end-to-end objective.

## K1.3 q16 source/scheduler integration

The complete current q16 chain is now integrated through commit `2d32d47e`.
It covers the literal Rust decoder and first-cap-203 loop, exact two-query
duplex blocks (including the sixteenth-draw extra-block boundary), native
block/chunk codecs, fixed-table callbacks, initial digests, scheduler replay,
the `64 × 8` forest, exact consumed prefixes, and the authenticated binary
frontier recurrence.

The strongest maintained endpoints include:

```text
strict_checked_refinement_exposes_exact_q16_decoder_prefixes
exact_compiler_trace_contains_each_q16_initial_output
exact_operational_q16_pointwise_implies_successful_forest
exact_operational_q16_output_forest_succeeds
```

The integrated maintained Lean 4.32 replay passed:

```text
unit: aspis-v7-one-tx-k13-q16-integrated-01
invocation: b4f4f174cb1f40ea96a8e573cf2a2e58
result: PASS (9,015 jobs)
wall: 20:02.56
/usr/time maximum RSS: 39,075,116 KiB
cgroup memory peak: 31.8 GiB
swap: 0
axiom union: propext, Classical.choice, Quot.sound
```

The large peak came from the pre-existing
`V7ExactCorrelatedAgreementInitialCurveBranch` dependency. The q16 targets
themselves completed in 2.6--2.8 seconds after that object existed. The live
cgroup was raised, without restarting the build, from 28 GiB to the authorized
48 GiB high/55 GiB maximum and retained zero swap.

The final Aeneas operational source bridge also passed under Lean 4.31:

```text
unit: aspis-v7-one-tx-q16-operational-source-02
invocation: 2f439cea7d6944e988fcba03f0738222
result: PASS
wall: 3.69 seconds
maximum RSS: 6,848,876 KiB
swap: 0
```

Its endpoint `raw_candidate_entry_and_trace_match_history_coverage` proves
literal translated candidate/squeeze execution from chronological ROM-history
coverage. The smallest remaining q16 composition lemma must construct the
candidate and squeeze membership facts from the actual exact-compiler history
and use them to identify the online routed forest with the canonical accepted
forest. Those membership/`covered` facts remain visible; they have not been
replaced by freshness, independence, or a conclusion-shaped premise.

The first exact-root part of that composition is now kernel checked in
`V7Tag73ExactCompilerQ16HistoryCoverage`:

```text
exact_operational_root_has_q16_history_alignment
exact_operational_verifier_history_is_table_covered
```

The focused NUC replay passed 9,000 jobs in 6.17 seconds with 6,912,168 KiB
maximum RSS, zero swap and the standard axiom union only. Thus the generic
history-coverage premise is discharged for the actual projected root. What
remains is occurrence/routing: literal candidate and squeeze pairs must be
located in that history, and an adversary-first query followed by a verifier
cache hit must be handled by the source-anchored cached-coordinate replay. It
would be unsound to classify that cache hit as a fresh verifier answer.

## K1.5 gamma actual-source alignment

The scheduler-native gamma replay and source alignment are integrated through
commit `14a718cd`. The cache/prequery case, cursor-relative continuation, and
actual-answer replay close without treating an adversary prequery as a rare
event. The integrated target
`AspisFormal.K1.V7Tag73ExactCompilerActualGammaReplayClosure` passed on the
NUC in 6:35.41 with a 2.1 GiB cgroup peak and zero swap. Its strongest endpoint
is `exact_compiler_actual_gamma_replay_closure`; the exact K1.5 raw value
remains `336869027002169 / (P^4 - 1)`.

This closes gamma source alignment, not all K1.5 probability accounting. The
eight fixed-category event inclusions and the restored residual-event measure
inclusion remain explicit gates.

## Remaining end-to-end proof gates

1. K1.3: compose the literal q16 callback history with the online routed forest
   and discharge the causal `covered` inclusion; then close the one-fold,
   joint-query batch and later-alpha actual-law inequalities.
2. K1.4: instantiate the width-29 variable-prefix causal law on the exact
   compiler/source execution.
3. K1.5: instantiate the eight fixed event inclusions and the restored-gamma
   residual inclusion. The exact raw error remains
   `336869027002169 / (P^4 - 1)` with no independence or work normalization.
4. Compose those concrete inequalities into the already-green K1.6 compiler
   capstone.
5. Remove or justify the remaining direct production-to-projection source
   seams for the selected evaluator and Pool caller.
6. Freeze two byte-identical clean Linux SBF builds and the eleven-case
   adversarial TxV1 bundle.
7. Run the same finalized one-transaction lifecycle on public devnet once its
   TxV1 execution feature is active. No transaction is signed or submitted by
   this evidence phase.
