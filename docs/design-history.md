# Design history

The default branch is the public Aspis Spend release surface. It keeps the
current implementation, the source modules required by the q18/g37 release,
the paper source, and the tooling that certifies and executes a release.

The pre-publication research tree is preserved by two immutable tags:

- [`research-archive-2026-07-14`](https://github.com/DJBarker87/aspis/tree/research-archive-2026-07-14)
  (commit `020f8f87238435dc2e1dc8cb41df90670fcb94f6`): the earlier root
  workspace, rejected parameter iterations, superseded certificates, negative
  experiments, and the full sequence of failed or abandoned designs.
- [`research-archive-2026-07-15`](https://github.com/DJBarker87/aspis/tree/research-archive-2026-07-15):
  the working tree immediately before the production-surface strip,
  including the local-validator measurement harness and the superseded
  design-iteration modules later removed from the default branch.

The archive is a set of Git tags rather than copied directories. This keeps
the default checkout focused; Git history remains the authoritative record
for individual changes and their chronology. During research the release now
named Aspis Spend was tracked under an internal iteration number, which
appears throughout the archived trees and their file names.
