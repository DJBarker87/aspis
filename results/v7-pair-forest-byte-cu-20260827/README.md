# V7 pair-forest byte-for-CU profile

This directory contains a default-off LiteSVM component profile for the
non-cryptographic ASQ8/ASF8/ASR8 transport and the byte-only eight-lane Pool
state wrapper.  It is pinned to source revision
`041780f4ef0be98c5b1675df87917046b62b4c2f`.

The frozen byte inventory is:

| Item | Bytes |
|---|---:|
| ASQ8 compact request | 320 |
| reconstructed ASF8 statement | 1,880 |
| ASR8 result | 792 |
| verifier-derived candidate afterstate | 688 |
| staged-pair proof body | 30,504 |
| upload payload | 31,192 |
| proof account | 31,232 |

The profile executes account, PDA, owner, registry, profile/release, codec,
copy, comparison, result-transport, lane/history, and nullifier plumbing.  It
does **not** execute Tag-73 cryptography: the normal ASQ8 handler still fails
closed with `V7_PAIR_FOREST_ASQ8_CRYPTO_NOT_INTEGRATED` after reconstructing
the statement.  The profile-only Pool encoder also skips the strict encoder's
20 Poseidon root reconstructions so those operations do not contaminate this
non-cryptographic component measurement.  A profile result therefore cannot
be reported as a combined verifier transaction.

The marker log calls are themselves metered.  The JSON evidence records both
the total profiled transaction and consecutive marker deltas so this overhead
remains visible.

## Host gates

- normal verifier ASQ8 focused tests: 6 passed;
- verifier profile focused check: passed;
- Pool profile focused tests: 1 passed (96 filtered);
- standalone LiteSVM harness check: passed;
- Solana program autofixer: zero issues in all five changed program Rust
  files, with no repeat requested.

The SBF/LiteSVM measurement remains deliberately separate from these host
gates and requires the two feature-gated SBF artifacts.
