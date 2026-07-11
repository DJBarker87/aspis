# Stwo line-FRI reproduction anchor

This directory retains the exact official-source generator used to anchor
Aspis's host line-FRI conformance corpus. It targets Stwo commit
`5d10e6b4baa559766e7bbae133b918121211a9c5`; it is a reproduction fixture, not
an Aspis production prover or verifier.

From a clean checkout:

```sh
git clone https://github.com/starkware-libs/stwo.git /tmp/stwo-line-fri-reference
git -C /tmp/stwo-line-fri-reference checkout 5d10e6b4baa559766e7bbae133b918121211a9c5
cp aspis/reference/stwo-line-fri/aspis_line_vectors.rs \
  /tmp/stwo-line-fri-reference/crates/stwo/examples/aspis_line_vectors.rs
cargo +nightly-2026-01-15 run --quiet --release --manifest-path \
  /tmp/stwo-line-fri-reference/Cargo.toml -p stwo \
  --features prover \
  --example aspis_line_vectors \
  > /tmp/aspis-stwo-line-fri-corpus.bin
```

Verify the binary corpus:

```sh
shasum -a 256 /tmp/aspis-stwo-line-fri-corpus.bin
```

Expected SHA-256:

```text
623df44fe1d5f9c5090e2b1301878f4308f1c6030314c515964e6b6e918801d8
```

The generator also prints the short human-readable vector used by the Rust
test when invoked with `-- show` after the example name.
