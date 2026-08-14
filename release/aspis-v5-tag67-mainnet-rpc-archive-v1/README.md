# Aspis V5 mainnet RPC archive

This additive release preserves the finalized RPC data needed to reconstruct
the V5 deployment and proof-upload history after the temporary accounts were
closed. It does not modify the immutable
`aspis-v5-tag67-mainnet-v1` release.

The capture completed on 25 July 2026 and contains:

- both paginated `getSignaturesForAddress` responses for payer
  `AXfWHFSF2F7gbwzdDfe8h5PHksePb3fLxSGsRpktbJ8p` (`1,000 + 570`
  signatures);
- a full finalized `getTransaction` response, using base64 transaction
  encoding, for every one of those `1,570` signatures;
- non-null transaction results for all `1,570` signatures;
- the full payer history from `2026-07-24T10:35:27Z` through the final sweep
  at `2026-07-25T00:01:06Z`;
- finalized account observations for the program, ProgramData, proof, payer,
  pool, and nullifier accounts; and
- the genesis hash and finalized observation slot.

The response archive includes the deployment buffer writes, the finalized
deployment, the 84-transaction spend lifecycle, and cleanup. In particular,
it contains the finalized Tag-67 spend at `2026-07-24T23:57:25Z` and the
ProgramData close at `2026-07-24T23:59:16Z`, 111 seconds later.

At capture time the ProgramData, proof, and payer account observations all
had a null account value. The raw history is therefore the durable
reconstruction route; those bytes can no longer be recovered from the live
account values.

## Files

- `rpc-cache/payer-full-rpc-responses.tar.gz` contains 1,581 raw, complete
  JSON-RPC responses: two signature pages, 1,570 transactions, eight account
  and chain observations, and the capture index.
- `rpc-cache/index.json` records every signature, slot, block time, response
  path, response byte count, and SHA-256 identity.
- `rpc-cache/archive-summary.json` gives the top-level counts and archive
  identity.
- `release-binding.json` binds the archive to the V5 release, its five named
  lifecycle transactions, and the published proof and statement identities.
- `verify.py` checks every archived member, parses every transaction wire, and
  confirms that the first signature bytes encode the indexed transaction id.
  It does not independently verify the Ed25519 signatures. It then reconstructs
  the exact released proof from the 79
  successful upload instructions, checks the statement against the landed
  Tag-67 wire and pool initialization, reconstructs the exact released SBF
  from the upgradeable-loader writes, and derives the complete loader-v3
  ProgramData image (including its zero padding to the deployed maximum data
  length).

Run:

```sh
python3 verify.py
```

The reconstruction currently yields:

- proof: 75,358 bytes, SHA-256
  `330414df587974684643a6062d092db0519d746f0c7efe4ed2108775b685feaf`;
- SBF: 1,258,496 bytes reconstructed from 1,466 successful writes (1,457
  unique writes plus nine byte-identical retries), SHA-256
  `4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`;
- loader-v3 ProgramData image: 1,300,045 bytes, SHA-256
  `3afcfd14786e86c6df6d72d3c7675f6dbed5574e021d833e01bf63578c1045f9`.

The ProgramData digest is an offline reconstruction from the archived
deployment instruction, loader writes, and loader-v3 account layout. It is not
a hash taken from a surviving live account: that account was closed 111
seconds after the spend.

To inspect the raw responses:

```sh
mkdir /tmp/aspis-v5-rpc-archive
tar -xzf rpc-cache/payer-full-rpc-responses.tar.gz \
  -C /tmp/aspis-v5-rpc-archive
```

The provider endpoint and API credential are deliberately absent from every
published file. The capture script is
`tools/archive_solana_address_history.py` at the repository root.
