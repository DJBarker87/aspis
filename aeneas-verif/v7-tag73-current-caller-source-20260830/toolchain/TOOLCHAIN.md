# Frozen source-bridge toolchain

## Charon and Rust

- Charon `0.1.223`, commit
  `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`.
- Charon binary SHA-256:
  `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`.
- Rust toolchain `nightly-2026-06-01`.
- `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with LLVM `22.1.6`.

## Aeneas

- Upstream commit: `d860ac47ed548d3da6d799afc013779ce470516c`.
- Patched Git tree: `031a61b263bffddabfd04e3476fb53a3754fdb64`.
- Version string: `d860ac47-tag73-looparity-r1`.
- Static binary SHA-256:
  `7a6633fbb01fad506336c1a1ef54382924d261fe0bf4ac1a8c8f119e90462a4a`.
- Pinned dependency image:
  `sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7`.

`BASE-PATCHES.sha256` freezes the accepted base patch sequence. The build then
applies `aeneas-d860ac47-array-default-excluded-trait.patch` and
`aeneas-d860ac47-loop-break-arity-preflight.patch`, and checks the resulting
Git tree before compiling. The loop patch guards Aeneas's optional loop-output
permutation with the break-payload arity invariant and otherwise selects its
existing no-reorder path. The separate
`aeneas-d860ac47-unbound-symbolic-diagnostic.patch` was used only to identify
the lost symbolic values; it is deliberately absent from the build script and
the accepted patch manifest.

`build-patched-aeneas-nuc.sh` checks every revision, patch digest, tree hash,
container image, version string, and output-binary digest. It must run inside
a zero-swap cgroup with `MemoryHigh=6G` and `MemoryMax=8G`.

## Generated Lean staging

Raw Aeneas output is immutable evidence. The accepted Lean 4.32 staging is
performed by `stage-current-helpersopaque-lean432.sh`. It applies only guarded,
source-equivalent compatibility rewrites already used by the preceding frozen
Tag-73 source bridge, validates and chunks the five generated circle tables,
validates and chunks the 15-entry atomic pattern registry, and imports literal
independent translations of the two helper functions.

The stage additionally checks and repairs the exact generated closure-product
precedence error, qualifies the exact 80 monadic `lift` calls that occur after
a Rust helper shadows that identifier, normalizes two exact no-op `FnMut`
callbacks, and supplies executable scalar/iterator standard-library models.
All occurrence counts are guarded; a changed generated shape fails staging.

Generated `*_Template.lean` files contain Aeneas's placeholder axioms and are
archival only. They are never present in the compile order and are explicitly
excluded from the accepted-source scan.

## Source normalization

`current-caller-aeneas-source-normalization.patch` is an extraction-only,
source-equivalent normalization applied to a disposable copy of revision
`bcd03b12293f2737dfa1da1436092a0a24a6ae24`. It is not applied to the
production worktree. The patch removes only two unsupported lowering shapes:

- a fixed four-byte `vec!` lowered through `Box<MaybeUninit<[u8; 4]>>`;
- four mutable-capture closures whose bodies are moved unchanged into
  ordinary explicit `&mut` helpers.

`apply-current-caller-source-normalization.sh` validates the two exact input
files, patch digest, revision when Git metadata is present, the two-path diff,
and all normalized key-source hashes. The focused release tests and focused
Charon/Aeneas translation must pass before the complete caller is translated.
This shim remains part of the ordinary source-tool trust base; it adds no
trusted verifier input and no mathematical or cryptographic premise.
