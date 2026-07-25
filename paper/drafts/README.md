# Publication drafts

This directory preserves dated manuscript drafts as review artifacts. They are
not immutable release papers and do not replace the living manuscript in
[`paper/aspis-spend/`](../aspis-spend/).

## Draft 0.1

[`aspis-paper-draft-0.1.pdf`](aspis-paper-draft-0.1.pdf) is the complete first
publication draft dated 25 July 2026.

- Size: 613,927 bytes
- SHA-256:
  `c6998b2f3651361a428aa2df417a33d3fead1b00c64ff737d96f9c05a17f1f5f`
- Pages: 29

Draft 0.1 deliberately predates the completed V5 release-record import. Its
mainnet appendix identifies the intended Tag-67 signature but leaves the
landed slot, compute use, program-data identity, proof digest, and post-state
as open publication tasks. Those facts are now finalized in the
[V5 mainnet record](../../docs/v5-mainnet-demo.md) and
[release bundle](../../release/aspis-v5-tag67-mainnet-v1/).

Use the [living manuscript](../aspis-spend/aspis-spend.pdf) for the current
paper text and Draft 0.1 only when reviewing the publication's development.
From this directory, `shasum -a 256 -c SHA256SUMS` checks the imported file.
