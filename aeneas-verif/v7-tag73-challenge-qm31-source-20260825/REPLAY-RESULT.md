# Focused replay result

- date: 2026-08-25
- systemd unit: `v7-tag73-qm31-replay-final8.scope`
- invocation ID: `f1dc0206c8aa4cd4b6ceb45b44b612a4`
- status: PASS, exit status 0
- cap: `MemoryMax=12G`, `MemorySwapMax=0`, `TasksMax=64`
- maximum RSS: 6,946,924 KiB
- swaps: 0
- elapsed wall time: 39.54 seconds
- canonical LLBC SHA-256:
  `0c9f44a7a426b7efd1404e8776795958d89f203eca2915994d013a756b27d857`

The replay recorded bundled `/translated/options/mir = null` and replayed
`/translated/options/mir = "Built"`, normalized only that whitelisted field,
and found the remaining structured LLBC tree byte-equal.  It then regenerated
and compared the Aeneas modules, rebuilt the four sampler modules and source
certificate, compiled the concrete callback replacement, and compiled the
unchanged compact `Types.lean` and `Funs.lean` against it.

The final printed callback theorem
`V7CompactSemanticFullGenerated.transcript.Transcript.challenge_qm31_is_source_generated`
depends only on `propext`, `Classical.choice`, and `Quot.sound`.  The checked
closure contains no `sorry`, `admit`, `axiom`, or `native_decide` proof
escape.  The remaining interface is the transcript's arbitrary total hash
callback; no SHA-256 security, collision-resistance, random-oracle, or
uniformity claim is made.

The complete output is in `logs/nuc-replay-final8.log`; the pre-normalization
structured diagnostic is in `logs/nuc-llbc-structured-diff.log`.
