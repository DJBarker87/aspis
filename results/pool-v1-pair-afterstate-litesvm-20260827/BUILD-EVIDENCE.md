# Build and run record

Commands used from the repository root:

```text
NO_DNA=1 CARGO_BUILD_JOBS=1 cargo-build-sbf --manifest-path programs/aspis-pool/Cargo.toml --features pair-afterstate-evidence --sbf-out-dir results/pool-v1-pair-afterstate-litesvm-20260827/artifacts
NO_DNA=1 CARGO_BUILD_JOBS=1 cargo-build-sbf --manifest-path results/pool-v1-pair-afterstate-litesvm-20260827/verifier-double/Cargo.toml --sbf-out-dir results/pool-v1-pair-afterstate-litesvm-20260827/artifacts -- --locked
cargo run --quiet --manifest-path results/pool-v1-pair-afterstate-litesvm-20260827/harness/Cargo.toml -- results/pool-v1-pair-afterstate-litesvm-20260827/artifacts/aspis_pool.so results/pool-v1-pair-afterstate-litesvm-20260827/artifacts/aspis_pair_afterstate_transport_double.so same-page results/pool-v1-pair-afterstate-litesvm-20260827/evidence-same-page.json
cargo run --quiet --manifest-path results/pool-v1-pair-afterstate-litesvm-20260827/harness/Cargo.toml -- results/pool-v1-pair-afterstate-litesvm-20260827/artifacts/aspis_pool.so results/pool-v1-pair-afterstate-litesvm-20260827/artifacts/aspis_pair_afterstate_transport_double.so rollover results/pool-v1-pair-afterstate-litesvm-20260827/evidence-rollover.json
cargo test -p aspis-pool pair_ --lib --features pair-afterstate-evidence
```

The final pool SBF build emitted no stack-offset or frame-clobber diagnostic.
The two generated keypair files were deleted immediately and are not part of
the evidence bundle.  The build artifacts are research-only and do not encode
or imply a deployment identity.
