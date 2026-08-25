# Patched Aeneas toolchain record

The sampler extraction was generated with a fresh isolated x86-64 static
Aeneas binary.  The shared translator binary and shared Aeneas checkout were
not modified.

- Aeneas base commit:
  `b59d5188c082f704a418c7cb4e52ad69328002d1`
- audited Lean-4.32/translator patch:
  `../../lean432/aeneas-b59d5188-lean432.patch`
- patch SHA-256:
  `5abaafc2d345511dda0eb96cd40154daff137f79dc4bcfa8247a45acea639c9c`
- patched git tree:
  `5a843e70672e4139232b2fdcb52a0c1fbd4b1619`
- static binary SHA-256:
  `4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5`
- binary version: `aeneas b59d5188-lean432-extended`
- binary format: statically linked x86-64 ELF, 49,419,624 bytes
- Charon commit:
  `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Charon binary SHA-256:
  `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`
- serialized Charon version: `0.1.223`
- container image:
  `ocaml/opam@sha256:42f6e13e9aceedc701eefdb89fca9fd1868c8cadd1144b334ca799474eadb702`
- container image ID:
  `sha256:98cb533c50c4dc82763cdf80920b3d4ba3fb7ac73f814e1193a817110d80d6ce`
- container architecture: x86-64
- OCaml: 5.2.1
- opam: 2.1.6
- dune: 3.24.2
- GCC: Debian 12.2.0
- Docker server: 29.1.3
- binary-build cgroup: 24 GiB memory, no additional swap
- proof/extraction cgroup: 12 GiB memory, zero swap
- Lean: 4.32.0, commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- Aeneas Lean source-tree aggregate SHA-256:
  `b98335b2ce64c0e72730159fc86987dd456b8d8dace6dd7a2cd9f5ccf5946433`
- Aeneas Lean `.olean` aggregate SHA-256:
  `cd6d2204d071615a7c386af875908c375f94a1f4bec456df49cc7b37fce11ef5`
- AspisFormal `lake-manifest.json` SHA-256:
  `65c23cce5c1bab2ba00affdff53fe52b67388cf2491c7f8ec68c1c2977dd7c10`

The patch is the already-audited V5 Lean-4.32 translator patch.  It extends
the existing symbolic loop/join translation and fixes Lean-4.32 backend
compatibility; it does not add a definition or axiom for
`Transcript::challenge_qm31`.  In this bundle the method, both loop bodies,
both loops, and `squeeze_block` are all generated transparently.  The only
external template entries are the source constants `P` and `M31::ZERO`, which
the checked module defines as `2147483647#u32` and `0#u32`.

`build-patched-aeneas.sh` reconstructs the exact temporary tree and copies
only the resulting static binary to the requested isolated output directory.
