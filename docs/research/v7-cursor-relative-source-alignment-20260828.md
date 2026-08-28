# V7 cursor-relative source-alignment audit (2026-08-28)

## Result

This checkpoint adds a source-neutral, proof-relevant cut for the literal
projected machine continuation and instantiates it on the exact deployed
adversary/verifier root.  It does not classify raw SHA inputs by future logical
role.

The main chain is:

1. `SourceAnchoredMachineCut.ofProjectedPrefix` constructs a cut from an
   existing executable `ProjectedMachinePrefixReturned` certificate.
2. `projected_fresh_returned_trace_table_exact` proves that the final immutable
   table is the current table followed by exactly the ordered future fresh
   input/answer entries.
3. `source_anchored_machine_cut_lookup_or_future_fresh` proves the requested
   cursor-relative cached-or-future-fresh dichotomy.
4. `projected_fresh_returned_trace_future_input_missing` proves that every
   future fresh coordinate is absent at the cut.
5. `source_anchored_machine_cut_advance_first_fresh` constructs the residual
   cut after one literal fresh step.  Cached normalization is table-inert and
   the actual head entry is appended exactly.
6. `projected_fresh_trace_scan_pauses_at_exact_future_answer` proves that the
   executable native scanner reaches a future coordinate and that the saved
   `pause.targetAnswer` is the exact actual answer.  It consumes no extra answer
   for cached calls.
7. `source_anchored_machine_cut_lookup_or_scan_pause` combines the table and
   scanner results into a reusable one-coordinate theorem.
8. `SourceAnchoredSequentialCut` joins two actual machine cuts at an exact
   intermediate oracle state.  Its ordered theorem routes a final answer to
   cache, the first actor suffix, or the second actor suffix.
9. `exactCompilerRootSourceAnchoredCut` constructs that joined cut from the
   production adversary and verifier prefixes.
10. `exact_compiler_final_lookup_in_ordered_root_suffix` removes the impossible
    empty-root cached branch and places the original exposure in the ordered
    adversary or verifier fresh list.
11. `exact_compiler_consumed_gamma_coordinates_ordered_root` applies the result
    to every output/advance coordinate consumed by the actual variable-prefix
    gamma decoder.
12. `exact_compiler_final_lookup_has_full_target_pause` erases the ordered
    source occurrence to the existing full operational trace and constructs an
    executable production-root pause.

The adversary-first/verifier-cache-hit path is preserved.  It has one original
fresh answer and a later cached use; it is neither rejected nor charged as a
bad event.

## Exact remaining boundary

`exact_compiler_actual_gamma_replay_closure` is not proved at this checkpoint.
The remaining gap is no longer final-table occurrence, chronological root
routing, scanner reachability, exact paused answer, or one-machine residual-cut
preservation.  It is the lift of the joined root certificate through each
evolving `SchedulerNativeGammaCursor`.

The smallest useful next semantic object is an exact-production alignment
between a gamma cursor and a split of the concatenated adversary/verifier fresh
coordinate list.  It must derive, rather than assume:

```lean
structure ExactCompilerRootGammaCursorAligned
    (input : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance sample)
    (state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)) where
  consumed future : List (ShaInput × Digest256)
  rootSplit :
    let prefixes := input.package.root.full.projection.rootPrefixes
    prefixes.adversary.freshQueries ++ prefixes.verifier.freshQueries =
      consumed ++ future
  cursorExact :
    state.cursor = schedulerNativePrefixCursor transitionFuel
      (exactPlainRomCursor configuration sample.1)
      (consumed.map Prod.snd)
  answersExact :
    let prefixes := input.package.root.full.projection.rootPrefixes
    state.remainingAnswers =
      future.map Prod.snd ++ prefixes.verifier.remaining
  tableExact :
    state.oracle.table = consumed.map projectedFreshEntry
```

The decisive preservation theorem then has the following shape:

```lean
theorem exact_compiler_actual_gamma_coordinate_step
    (aligned : ExactCompilerRootGammaCursorAligned input state)
    (kind : SchedulerNativeGammaQueryKind)
    (target : ShaInput) (answer : Digest256)
    (found :
      tableLookup (exactOperationalTable input) target = some answer) :
    ∃ next,
      consumeSchedulerNativeGammaCoordinate transitionFuel kind
          target answer state = .ok next ∧
      ExactCompilerRootGammaCursorAligned input next
```

This theorem must handle a target already behind the cursor as cached, later in
the current actor suffix, or later across the adversary-to-verifier transition.
Whole-run membership alone cannot distinguish those cases.  The new exact
paused-answer and residual-cut theorems discharge the one-machine part; the
joined-prefix-to-evolving-gamma-cursor preservation is still missing.

This is a **semantic-model/source-alignment deficiency**.  No probability,
root-counting, Rust protocol, wire, CU, or cryptographic limitation has been
identified.

## Rejected shortcuts

- No raw-coordinate or history-coordinate role classifier.
- No requirement that first exposure be verifier-origin.
- No negligible charge for adversarial prequery.
- No independence, grinding normalization, or extra union bound.
- No caller-supplied replay equality or abstract restore oracle.
- No equality between `rawCalls` and `verifierHistory`.

## Accounting and source boundaries

This work changes no K1.5 or K1.6 numerical bound.  The K1.5 raw expression
remains

```text
336869027002169 / (P^4 - 1)
```

The actual-law `fixedBounds` and `restoredBound` premises therefore remain, and
the corrected K1.6 capstone still takes the genuine K1.3, K1.4, and K1.5
bounds.  Current-source fixed-field decode and parsed-wire projection remain
separate Aeneas/source obligations and are not fields of the scheduler cut.

## Verification

Both new Lean leaves contain `#print axioms` for their principal theorems.
The observed union is:

```text
propext
Classical.choice
Quot.sound
```

Focused replay timings and memory measurements are recorded in the final task
report.  No `sorry`, `admit`, `sorryAx`, `native_decide`, or project axiom is
used.
