# Current-source A/B/C and Tag-67 capstone

`proof/CurrentSourceABCapstone.lean` is the final combined theorem. Run
`replay-lean432.sh` with Lean 4.32. The replay rebuilds the direct Component-B,
Component-C, and Tag-67 boundaries, then audits the combined theorem under
default limits.

The `gooda-generated-split-root/` directory is the curated source closure for
the authenticated Component-A theorem. Its additive namespace is mechanically
retargeted from `AuthenticFieldSub` to the equivalent current
`AspisCoreAdditive` boundary used by the combined environment. The generated
Good-A kernels are large, so the ordinary combined replay consumes their
previously audited Lean-4.32 object cache. Set `GOOD_A_OLEAN_DIR` when that
cache is not present at the historical local extraction path.

The combined theorem's only Tag-67 implementation/model correspondence premise
is the exact grinding `HashFn` application equation recorded in the release
preflight. No parser, projection, digest-predicate, or six-step correspondence
premise is accepted.
