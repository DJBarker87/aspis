# Research archive

The public default branch contains the current release implementation and
its supporting release machinery. Earlier experiments are retained in Git,
not copied into this directory.

The immutable
[`research-archive-2026-07-14`](https://github.com/DJBarker87/aspis/tree/research-archive-2026-07-14)
tag contains these historical categories:

- rejected parameter profiles and superseded release certificates;
- failed or abandoned protocol and verifier designs;
- exploratory Stage 0/1/2 measurement artifacts;
- earlier workspace layouts and one-off research tooling; and
- regression fixtures that were not required on the public release surface.

The immutable
[`research-archive-2026-07-15`](https://github.com/DJBarker87/aspis/tree/research-archive-2026-07-15)
tag is the working tree immediately before the production-surface strip. It
contains the research measurement harness removed from `xtask` (the stage
0–2 measurement subcommands and the local-validator measurement module), the
superseded design-iteration code later removed from all crates, and the
first-generation release evidence with its documents and certificates. The
historical measurement and reproduction commands recorded there run from
that tag.

The immutable
[`research-archive-v5-production-closure-2026-07-22`](https://github.com/DJBarker87/aspis/releases/tag/research-archive-v5-production-closure-2026-07-22)
release and
[matching tag](https://github.com/DJBarker87/aspis/tree/research-archive-v5-production-closure-2026-07-22)
contain the complete V5 production-closure workspace before publication
curation. It preserves every LLBC blob, raw and versioned Aeneas translation,
extraction log, superseded retarget experiment, and intermediate V5
feature-build directory. The default branch retains the final normalized Lean,
proof source, integration theorems, reports, canonical SBF, and CU evidence.
The tag is pinned to full commit
[`859d8588d2761fac6714226877c9317f7d697a03`](https://github.com/DJBarker87/aspis/commit/859d8588d2761fac6714226877c9317f7d697a03).
Its deterministic archive identity is recorded in
[`v5-production-closure-2026-07-22-manifest.json`](v5-production-closure-2026-07-22-manifest.json).

## Final V5 end-to-end record

The immutable
[`aspis-v5-formalization-paper-v1`](https://github.com/DJBarker87/aspis/tree/aspis-v5-formalization-paper-v1)
tag preserves the frozen end-to-end V5 formalization publication at commit
`105738ebe0758fd31edbb76f6735c7f5da96dbdd`. The maintained
`aspis-spend` branch adds only later publication maintenance, including the
author contact rendered into the PDF.

The `archive/v5-end-to-end-20260827` branch additionally retains the useful
Component B/C design audits, exact matrix/rank certificates, and compute-unit
probes that were left in the final V5 workspace. Their own status fields are
authoritative: several are explicitly provisional or stale-schedule research
evidence and are not part of the deployed end-to-end claim.

Independent V5 proof-development tips that were not ancestors of a public
branch are mirrored under `archive/v5/` on the origin remote. Those refs are
historical preservation points, not an assertion that every experiment was
accepted into the final theorem.

Use the tags when reproducing research history. Use the default branch for
the current implementation. Git history is the authoritative per-change
record.

## V5 Component-C q18 frozen maps

The V6 integration also retains the final V5 Component-C q18 matrix and
quotient-obstruction artifacts under `results/spend/`. Their exact paths,
sizes and SHA-256 identities are pinned in
[`v5-component-c-frozen-q18-2026-08-25-manifest.json`](v5-component-c-frozen-q18-2026-08-25-manifest.json).
They remain V5 evidence and are not inputs to the V6 verifier.
