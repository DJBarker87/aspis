# V7 one-transaction candidate preflight

This directory freezes the inputs needed to reproduce the selected V7
eight-lane Pool and Tag-73 verifier binaries at Pool source commit `da77d5f5`.
It also binds the deterministic eleven-case transaction fixture for the
atomic-marker lifecycle. It is deliberately a preflight, not a release bundle
or deployment authorization.

Run the source/evidence audit on any host:

```sh
release/v7-one-tx-candidate-preflight-v1/verify-inputs.sh
```

Run the two-copy Linux build only inside the required capped cgroup:

```sh
ASPIS_V7_TOOLCHAIN_CAPTURE_ROOT=<frozen-toolchain-capture> \
  scripts/v7_one_tx_release_replay.sh build <new-output-directory>
```

The capture must match the platform-specific Linux x86_64 v1.48 inventory in
`linux-x86_64-sbf-toolchain-v1.48.json` byte for byte. The historical V5
Darwin arm64 inventory is preserved in its original release directory but is
not a valid input to this Linux replay.

The exact eleven-case Agave suite additionally requires an Agave 4.2+ binary
directory. The replay materializes the committed fixture template against the
fresh byte-identical SBFs before execution:

```sh
ASPIS_V7_TOOLCHAIN_CAPTURE_ROOT=<frozen-toolchain-capture> \
  scripts/v7_one_tx_release_replay.sh build-and-simulate \
  <new-output-directory> <agave-4.2+-bin-directory>
```

The Pool SBF identity is intentionally not inherited from the superseded
pre-marker candidate. The first capped dual Linux run derives and records the
new Pool hash; the unchanged verifier must still match its frozen reference.
Both modes validate the fixture offline and require all seven negative cases
to assert exact protected-account rollback. Agave execution and fresh combined
CU remain open until the `build-and-simulate` mode succeeds.

All paths are fail-closed. No command in this preflight signs, submits, deploys
or mutates a public cluster.
