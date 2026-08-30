# Pool V1 verifier-registry focused SBF evidence

Date: 25 August 2026

Scope: one focused build of `programs/aspis-registry`. This is build evidence,
not deployment or transaction evidence.

The host gate passed 10/10 registry tests, the focused shared-statement helper
test passed 1/1, crate-local `cargo check` and Clippy with warnings denied
passed, and the Solana autofixer reported zero issues and zero suggestions.

The first SBF attempt stopped at a `no_std` macro import error. The only source
change was a Solana-target-gated `alloc::format` import. The authorized retry
ran on the dedicated Linux build host as systemd unit
`aspis-registry-sbf-20260825-a2.scope` with `MemoryMax=6G`,
`MemorySwapMax=0`, `NO_DNA=1`, and `CARGO_BUILD_JOBS=1`.

- Result: success
- Invocation: `215738a0cb3d4489a498148482bcbdab`
- Maximum RSS: 199,916 KiB
- Swaps: 0
- Artifact: `aspis_registry.so`
- Artifact bytes: 102,648
- Artifact SHA-256:
  `1066ffc4bf8a12a0ea56b64474b70e172162fc7852b66293c0c8c5f1380f0ff6`
- Build-log bytes: 16,169
- Build-log SHA-256:
  `f0cecfa2666185a8a98ed87478b9393511a78aabe00aa69833ee3f299c9b3a85`

The artifact remains in the isolated NUC build copy at
`<build-root>/target/deploy/aspis_registry.so`.
It has not been deployed or submitted to any cluster.

Remaining registry gates are the exact runtime lifecycle/System-CPI rollback
test, a reproducible second build for the final release artifact, deployment
identity and upgrade-authority policy, and finalized devnet evidence.
