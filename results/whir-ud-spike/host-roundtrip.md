# WHIR-UD Host Roundtrip

Generated: `2026-04-20T09:50:41.580888+00:00`

Reference: `https://github.com/WizardOfMenlo/whir` at `0aeaa7f337c743d9ddfcb9d909628d6491e3355c`

Field selection: Goldilocks2 confirmed after Phase 1: base Goldilocks source field with quadratic extension target field.

## Notes

- Current upstream Merkle/PoW hash mode observed through the host crate: Blake3.
- The transcript duplex remains Shake128 and domain-separator hashing remains SHA3, regardless of the Blake3 Merkle/PoW setting.
- Successful roundtrips use unchanged upstream proof objects at the byte level within the chosen ciborium serialization wrapper; no proof bytes are rewritten between reference verify and mirror verify.

## Attempt Matrix

| id | status | achieved bits | d | rate | proof bytes | ref hashes | mirror hashes | notes |
| --- | --- | ---: | ---: | --- | ---: | ---: | ---: | --- |
| whir-ud-goldilocks2-t100-rate1over2-d4-e1-l0-i4-k4-ascending | ok | 100.00 | 4 | 1/2 | 24896 | 195 | 195 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t100-rate1over2-d8-e1-l0-i4-k4-affine3x5 | ok | 100.00 | 8 | 1/2 | 47600 | 329 | 329 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t100-rate1over2-d12-e1-l0-i4-k4-quadratic7 | ok | 100.00 | 12 | 1/2 | 79936 | 1023 | 1023 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t100-rate1over4-d4-e1-l0-i4-k4-affine3x5 | ok | 100.00 | 4 | 1/4 | 15296 | 122 | 122 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t100-rate1over4-d8-e2-l0-i4-k4-quadratic7 | ok | 100.00 | 8 | 1/4 | 37392 | 297 | 297 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t100-rate1over4-d12-e1-l0-i4-k4-ascending | ok | 100.00 | 12 | 1/4 | 75232 | 1079 | 1079 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t100-rate1over16-d4-e1-l0-i4-k4-ascending | ok | 100.00 | 4 | 1/16 | 11456 | 104 | 104 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t100-rate1over16-d8-e1-l0-i4-k4-affine3x5 | ok | 100.00 | 8 | 1/16 | 37040 | 445 | 445 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t100-rate1over16-d12-e1-l0-i4-k4-quadratic7 | ok | 100.00 | 12 | 1/16 | 83776 | 1448 | 1448 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t128-rate1over2-d4-e1-l0-i4-k4-affine3x5 | ok | 128.00 | 4 | 1/2 | 33632 | 267 | 267 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t128-rate1over2-d8-e1-l0-i4-k4-quadratic7 | ok | 128.00 | 8 | 1/2 | 64304 | 436 | 436 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t128-rate1over2-d12-e1-l1-i4-k4-ascending | ok | 128.00 | 12 | 1/2 | 103584 | 1210 | 1210 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t128-rate1over4-d4-e1-l0-i4-k4-quadratic7 | ok | 128.00 | 4 | 1/4 | 20704 | 168 | 168 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t128-rate1over4-d8-e2-l0-i4-k4-ascending | ok | 128.00 | 8 | 1/4 | 50320 | 378 | 378 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t128-rate1over4-d12-e1-l1-i4-k4-affine3x5 | ok | 128.00 | 12 | 1/4 | 97344 | 1337 | 1337 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t128-rate1over16-d4-e1-l0-i4-k4-affine3x5 | ok | 128.00 | 4 | 1/16 | 15456 | 139 | 139 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t128-rate1over16-d8-e1-l0-i4-k4-quadratic7 | ok | 128.00 | 8 | 1/16 | 48368 | 552 | 552 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t128-rate1over16-d12-e1-l1-i4-k4-ascending | ok | 128.00 | 12 | 1/16 | 109472 | 1852 | 1852 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t100-rate1over2-d18-e1-l0-i4-k4-affine3x5 | ok | 100.00 | 18 | 1/2 | 175520 | 3571 | 3571 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t100-rate1over4-d18-e1-l0-i4-k4-affine3x5 | ok | 100.00 | 18 | 1/4 | 163680 | 3376 | 3376 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t128-rate1over2-d18-e1-l0-i4-k4-affine3x5 | ok | 128.00 | 18 | 1/2 | 227792 | 4552 | 4552 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |
| whir-ud-goldilocks2-t128-rate1over4-d18-e1-l0-i4-k4-affine3x5 | ok | 128.00 | 18 | 1/4 | 213904 | 4358 | 4358 | Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format. |

## Divergences

- None.
