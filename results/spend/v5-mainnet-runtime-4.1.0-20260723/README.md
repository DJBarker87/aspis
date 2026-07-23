# V5 replay on the current mainnet runtime

On 2026-07-23 Solana mainnet-beta reported Agave `4.1.0`, feature set
`3345198602`. The exact V5 SBF
`4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`
was replayed against the official Agave 4.1.0 validator across all three
selectors and every accepted marker-state path.

Each missing-marker execution completed the real System Program CPI three
times. The three selector totals were 1,331,178, 1,333,842, and 1,326,426 CU,
exactly 54 CU below the corresponding 2.3.13 measurements. The
present-marker control remained exactly 1,328,897 CU. The difference is the
runtime invocation charge, which changed from 1,000 to 946 CU. The SHA-256
charge used by the topology derivation remains 149 CU for a 129-byte
single-slice parent hash.

The one-lamport prefunded System-owned marker takes the longest accepted
marker path: transfer to rent exemption, allocate, then assign. The exact
mainnet transaction shape places a compute-unit price instruction before Tag
67. It measured 1,334,528, 1,337,192, and 1,329,776 CU across the three
selectors. The price instruction adds 150 CU and the prefunded marker path
adds 3,200 CU over the priced missing-marker path. Applying the existing
topology and GoodA/GoodB reserves gives a final 1,356,912-CU accepted-state
ceiling with 43,088 CU of headroom.
[`runtime-replay.json`](runtime-replay.json) records the runtime identity,
release hashes, replay inputs, measurements, and pinned source references.
[`prefunded-system-marker-cu.json`](prefunded-system-marker-cu.json) records
the exact instruction order, per-selector logs, and arithmetic; its SHA-256 is
`2d62930963fa67b247a746ec81e3b1614391710a69df528fc2a28361407e819f`.

The replay command for each selector was:

```sh
PATH="$AGAVE_4_1_BIN:$PATH" \
V5_CU_FROZEN_DIR="$FROZEN_DIR" \
V5_CU_PREBUILT_SBF_SHA256=4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40 \
V5_CU_FROZEN_MARKER_MODE=missing \
NO_DNA=1 \
cargo test --release -p aspis-xtask \
  v5_cu_probe::tests::v5_frozen_artifact_marker_mode_cu_measurement \
  -- --ignored --exact --nocapture
```

`$FROZEN_DIR` contains the release SBF and the selected proof and statement
under the fixture names expected by the test. The program-owned control uses
the same command with `V5_CU_FROZEN_MARKER_MODE=present`. The exact priced
prefunded replay uses `V5_CU_FROZEN_MARKER_MODE=prefunded` and
`V5_CU_COMPUTE_UNIT_PRICE_MICROLAMPORTS=1`.

No on-chain state was changed by this replay. The mainnet execution path
still verifies the deployed bytes and simulates the exact signed Tag-67
transaction before submitting the same wire.
