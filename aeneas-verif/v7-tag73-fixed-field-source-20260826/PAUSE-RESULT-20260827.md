# Moving-source pause result (2026-08-27)

This bundle is paused before generated Lean/source-theorem work because the
production transaction implementation advanced after the required worktree
base was frozen.

## Source revisions

- Audited/extracted snapshot: `921dcd2d6565fbcc504d8027e714237fb4ab83cf`
- Latest locally known `origin/v7/split-tensor` at the pause:
  `067b057826b4d73f037ed16a8a61550a91bf2e61`
- The latter changes `v7_onefold.rs`, `v6_transcript.rs`, and `sumcheck.rs`.
- The `parse_deferred_canonicality` byte layout is semantically unchanged in
  that diff, but the accepted verifier caller materially changes Tag-73
  relation/query-batch handling. Therefore generated Lean and the final
  literal-success theorem must be regenerated from the eventual frozen
  transaction revision.

## Reusable extraction result

Focused Charon extraction of the two production roots succeeded. The combined
LLBC SHA-256 is:

`31aced486cd1208386b05e1659b87c2d1353603be9aa411b99b430d9a71ff1de`

The candidate Aeneas compatibility delta from the existing ten-patch baseline
is preserved as:

`toolchain/aeneas-d860ac47-nested-shared-loop-normalization.patch`

Patch SHA-256:

`b8d08946d441057c31e30eee5563d97b889a1f303556553f58a1ba487a340c07`

`patch --dry-run -p1` succeeds against the ten-patch Aeneas baseline. This is a
candidate patch, intentionally not added to the final replay series while the
production revision is moving.

## Latest focused Aeneas replay

The corrected locally rebuilt Aeneas binary was used, not the stale binary in
the repository-level `_build` directory. The run advanced past the earlier
`sumcheck.rs:1620` singleton-shared-borrow mismatch, validating that narrow
comparison normalization. It then stopped on a distinct representation
mismatch at `sumcheck.rs:727:20-734:21`: the source retains two endable nested
component abstractions while the projected target has their safely collapsed
single abstraction.

- Exit status: `2`
- Wall time: `535.86 s`
- User time: `532.49 s`
- System time: `1.36 s`
- Maximum RSS: `1,711,407,104 bytes`
- Peak memory footprint: `1,740,588,664 bytes`
- Swaps: `0`
- OOM: no

No further compatibility work, generated-source freezing, or old-revision
Lean source theorem will be performed until a stable production commit is
selected.
