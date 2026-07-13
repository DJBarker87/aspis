# Official Stwo circle-candidate digest anchor

This directory retains the exact official-source generator for Aspis's
host-only circle encoder candidate. It targets Stwo commit
`5d10e6b4baa559766e7bbae133b918121211a9c5` and uses the candidate's fixed
49-column C1, two-helper C2, leaf-order, and layer-tag fixture. It does not
construct or validate an Aspis proof.

From the Aspis repository root:

```sh
git clone https://github.com/starkware-libs/stwo.git /tmp/stwo-circle-candidate
git -C /tmp/stwo-circle-candidate checkout 5d10e6b4baa559766e7bbae133b918121211a9c5
cp aspis/reference/stwo-circle-candidate/aspis_circle_candidate_digests.rs \
  /tmp/stwo-circle-candidate/crates/stwo/examples/aspis_circle_candidate_digests.rs
cargo +nightly-2026-01-15 run --quiet --release --manifest-path \
  /tmp/stwo-circle-candidate/Cargo.toml -p stwo --features prover \
  --example aspis_circle_candidate_digests \
  > /tmp/aspis-stwo-circle-candidate-digests.json
shasum -a 256 /tmp/aspis-stwo-circle-candidate-digests.json
```

Expected stdout SHA-256:

```text
3fd2d6a5ad480ef9e34fc8f5ac5b10101c86ddf4c1938f87afe076bbd49c29c7
```

Expected digest object:

```json
{
  "c1_codewords_sha256": "eb398b5bf27587d3d4abb693287530dc8aacc4f8ed0470b3e9133d331d2694ea",
  "c2_codewords_sha256": "7badaace498a8a1837b9f018dffe193ba1cb3528646578439391aecffbcc34a2",
  "c1_leaves_sha256": "2f0dc5ce5f7bdc604e544bc01c9d42b8d24bc8caf15625bd6e2336324c4adb69",
  "c2_leaves_sha256": "1be451ce4ff8a8a7ece496eb6ec05ead3de4645238d02c35a5b75ca1050c90c5",
  "c1_root": "c6a93117eb8ccd3e0e9c3ff9598ce6f34682f82c430a955da1c0f799c6c2ad4f",
  "c2_root": "c764cdff2474ee79b56fe9baeaa3c7cc5e62c2ae3b1f0ed470c00c28f83930b3",
  "fixture_sha256": "a130a5cb2bb8055423d5db9bc0ebbf563ef00e651efd6ee989816178bdc3c671"
}
```

The example uses official `CpuCirclePoly::evaluate` over
`CanonicCoset::new(12).circle_domain()`. C2 is evaluated as four official M31
coordinate polynomials. Its dependency-free SHA-256 implementation first
checks the standard `SHA256("abc")` vector.
