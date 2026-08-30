# V7 one-transaction candidate preflight

This directory freezes the inputs needed to reproduce the selected V7
eight-lane Pool and Tag-73 verifier binaries. It is deliberately a preflight,
not a release bundle or deployment authorization.

Run the source/evidence audit on any host:

```sh
release/v7-one-tx-candidate-preflight-v1/verify-inputs.sh
```

Run the two-copy Linux build only inside the required capped cgroup:

```sh
ASPIS_V7_TOOLCHAIN_CAPTURE_ROOT=<frozen-toolchain-capture> \
  scripts/v7_one_tx_release_replay.sh build <new-output-directory>
```

The exact eleven-case Agave suite additionally requires an Agave 4.2+ binary
directory and a complete case bundle satisfying the schema enforced by
`scripts/v7_txv1_disposable_agave_simulate.sh`:

```sh
ASPIS_V7_TOOLCHAIN_CAPTURE_ROOT=<frozen-toolchain-capture> \
  scripts/v7_one_tx_release_replay.sh build-and-simulate \
  <new-output-directory> <agave-4.2+-bin-directory> <case-bundle-directory>
```

All paths are fail-closed. No command in this preflight signs, submits, deploys
or mutates a public cluster.
