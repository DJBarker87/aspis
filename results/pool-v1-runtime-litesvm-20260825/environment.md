# Focused runtime environment

Harness host:

```text
OS: macOS 26.5 (25F71), arm64
rustc: 1.93.0 (254b59607 2026-01-19)
cargo: 1.93.0 (083ac5135 2025-12-15)
NO_DNA: 1
CARGO_BUILD_JOBS: 1
LiteSVM: 0.16.0
Agave runtime packages selected by LiteSVM: 4.2.1
```

SBF toolchain used for the test-only verifier transport double:

```text
solana-cargo-build-sbf: 2.3.0
platform-tools: 1.48
platform-tools rustc: 1.84.1
```

The exact Rust dependency resolutions are frozen by the two `Cargo.lock`
files in `harness/` and `harness/mock-verifier/`. The production Pool SBF
build environment and final artifact digest will be recorded after the
post-optimization isolated source build.

The harness uses a 1,400,000-CU compute-budget instruction and includes that
instruction in every recorded legacy and v0+ALT wire-size calculation.
