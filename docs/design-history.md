# Design history

The default branch is the public Profile 23 release surface. It keeps the
current implementation, the source modules still required by q18, the paper,
and the evidence needed to audit the published result.

The complete pre-publication research tree is preserved by the immutable
[`research-archive-2026-07-14`](https://github.com/DJBarker87/zk/tree/research-archive-2026-07-14)
tag at commit `020f8f87238435dc2e1dc8cb41df90670fcb94f6`. It contains the earlier
root workspace, rejected parameter profiles, superseded certificates,
negative experiments, and the full sequence of failed or abandoned designs.

The archive is a Git tag rather than a copied directory. This keeps the
default checkout focused and avoids duplicating hundreds of megabytes of old
build products. Git history remains the authoritative record for individual
changes and their chronology.

Profile 20--22 modules that remain on the default branch are dependencies or
regression fixtures used by Profile 23. Their presence does not make them
current releases.
