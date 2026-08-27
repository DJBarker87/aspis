# Pool pair-parent SBF CU probe

This focused diagnostic measures the literal production
`aspis_statement::pool_v1::pool_v1_tree_parent` function for 0, 1, 20, 21 and
40 calls. It runs only in local LiteSVM and never submits a transaction.

The program is a root-workspace member so that `cargo-build-sbf` consumes the
same pinned dependency graph as production. The harness is intentionally a
separate workspace because it executes the Agave 4.2.1 LiteSVM runtime.

Build and replay:

```sh
NO_DNA=1 CARGO_BUILD_JOBS=2 cargo-build-sbf \
  --manifest-path audit/poseidon-pair-probe/program/Cargo.toml \
  --sbf-out-dir audit/poseidon-pair-probe/target/deploy -- --locked

cargo run --offline \
  --manifest-path audit/poseidon-pair-probe/harness/Cargo.toml -- \
  audit/poseidon-pair-probe/target/deploy/aspis_poseidon_pair_probe.so
```

Expected output:

```text
count=0 cu=407
count=1 cu=23886
count=20 cu=469798
count=21 cu=493270
count=40 cu=939210
```

The measured marginal cost is 469,391 CU for twenty parents and 492,863 CU
for a pair compression plus twenty parents. See `evidence.json` for exact
toolchains and hashes. The checked-in evidence excludes the `.so` and Cargo
target directories.
