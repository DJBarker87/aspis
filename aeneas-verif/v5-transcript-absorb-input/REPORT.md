# V5 transcript root-absorb correspondence

Status: **source-authentic and kernel-checked**

The production verifier computes each root-absorption payload through the pure
helpers extracted here:

- round root: label `12`, `layer || root || public_fs_salt` (65 bytes);
- C2 root: label `13`, `root || public_fs_salt` (64 bytes).

Pinned Charon/Aeneas extraction covers both helpers and both label constants.
[`proof/V5TranscriptAbsorbInputProof.lean`](proof/V5TranscriptAbsorbInputProof.lean)
proves the exact labels and bytes for arbitrary roots and salts, and proves the
labels are distinct. The account-level composition also binds these payloads
to the 6,423-byte prefix parser, five public-salt windows, five private-root
windows, and the C1/C2 prefix/private-root equality check.

The exported theorem closures use only
`{propext, Classical.choice, Quot.sound}`.

## Provenance

- verifier source SHA-256:
  `213eb050c6cb5b6bb89ae02419c1efebe280fd51871755b37abf2fe56601e800`
- normalized generated module SHA-256:
  `999c9f6e19d52e9a08157969fdccb563f5e748c337da5be179760afcad3a211f`
- proof SHA-256:
  `ad838cf516b2362ce6761b0fc766de261702b0e2f0fe91227d8a4176ff795112`
- Charon: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Aeneas: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Rust: `nightly-2026-06-01`
- proof replay: Lean `4.32.0`

The normalized generated Lean and proof stay on `main`. The authenticated LLBC
and raw translation are retained at
[`research-archive-v5-production-closure-2026-07-22`](https://github.com/DJBarker87/aspis/tree/research-archive-v5-production-closure-2026-07-22).

## Boundary

This theorem proves the input passed to `Transcript::absorb`. The hash-function
implementation, transcript state transition, cross-call Fiat–Shamir order, and
cryptographic hash/PCS assumptions are composed at their respective higher
layers rather than duplicated here.
