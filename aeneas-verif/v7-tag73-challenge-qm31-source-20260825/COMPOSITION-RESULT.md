# Accepted-source composition result

- date: 2026-08-25
- systemd unit: `v7-tag73-qm31-accepted-source-compose03.scope`
- invocation ID: `d6ed89dbb0094bd68770117a37ed1767`
- status: PASS, exit status 0
- cap: `MemoryMax=12G`, `MemorySwapMax=0`, `TasksMax=64`
- maximum RSS: 2,699,552 KiB
- swaps: 0
- elapsed wall time: 7.35 seconds
- production source-bridge SHA-256:
  `1e45009650690933eca7e3b4e5535632ce1f9023510dbfd637f1145e10722732`
- compiled source-bridge olean SHA-256:
  `d98432f89146ccf88f28e06ae742c023646f20dcfef9026ed5fb1d1005c82e4d`

The exact production `V7CompactSemanticSourceBridge.lean` compiled with a
single temporary module root containing the separately hash-checked concrete
replacement `Types.olean` and `FunsExternal.olean` plus the unchanged compact
`Funs.olean`.  No production source file was modified.

The kernel reported exactly `propext`, `Classical.choice`, and `Quot.sound`
for each public accepted-source theorem:

- `accepted_execution_prefix_eta_eq`;
- `accepted_main_exposes_exact_outer_trace`; and
- `accepted_main_exposes_exact_prefix_eta`.

The concrete `challenge_qm31_is_source_generated` replacement certificate
has the same standard axiom inventory.  The former opaque
`transcript.Transcript.challenge_qm31` callback is absent from every audited
axiom set.  The sole remaining interface is the transcript record's explicit
arbitrary total hash function; no cryptographic security property is claimed.

The full bounded replay output is in
`logs/nuc-accepted-source-composition03.log`, and the unfiltered kernel axiom
output is in `logs/V7CompactSemanticSourceBridge.axioms.log`.
