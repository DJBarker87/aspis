# WHIR-UD SBF Projections

Generated: `2026-04-20T09:50:42.244308+00:00`

Compilation status: `failed`

Methodology: Direct SBF compilation was attempted on a minimal wrapper program. Quantitative CU numbers are lower bounds only: verifier hash count multiplied by the SHA syscall floor (148 CU/hash). No Goldilocks-specific arithmetic coefficient was available, and actual WHIR-UD hashes are Blake3/Shake128/SHA3 in software, so real CU is higher than the reported floor.

## Ranked Candidates

| rank | id | d | proof bytes | verifier hashes | hash floor CU | floor margin vs 1.4M |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | whir-ud-goldilocks2-t100-rate1over16-d4-e1-l0-i4-k4-ascending | 4 | 11456 | 104 | 15392 | 1384608 |
| 2 | whir-ud-goldilocks2-t100-rate1over4-d4-e1-l0-i4-k4-affine3x5 | 4 | 15296 | 122 | 18056 | 1381944 |
| 3 | whir-ud-goldilocks2-t128-rate1over16-d4-e1-l0-i4-k4-affine3x5 | 4 | 15456 | 139 | 20572 | 1379428 |
| 4 | whir-ud-goldilocks2-t128-rate1over4-d4-e1-l0-i4-k4-quadratic7 | 4 | 20704 | 168 | 24864 | 1375136 |
| 5 | whir-ud-goldilocks2-t100-rate1over2-d4-e1-l0-i4-k4-ascending | 4 | 24896 | 195 | 28860 | 1371140 |
| 6 | whir-ud-goldilocks2-t128-rate1over2-d4-e1-l0-i4-k4-affine3x5 | 4 | 33632 | 267 | 39516 | 1360484 |
| 7 | whir-ud-goldilocks2-t100-rate1over4-d8-e2-l0-i4-k4-quadratic7 | 8 | 37392 | 297 | 43956 | 1356044 |
| 8 | whir-ud-goldilocks2-t100-rate1over2-d8-e1-l0-i4-k4-affine3x5 | 8 | 47600 | 329 | 48692 | 1351308 |
| 9 | whir-ud-goldilocks2-t128-rate1over4-d8-e2-l0-i4-k4-ascending | 8 | 50320 | 378 | 55944 | 1344056 |
| 10 | whir-ud-goldilocks2-t128-rate1over2-d8-e1-l0-i4-k4-quadratic7 | 8 | 64304 | 436 | 64528 | 1335472 |
| 11 | whir-ud-goldilocks2-t100-rate1over16-d8-e1-l0-i4-k4-affine3x5 | 8 | 37040 | 445 | 65860 | 1334140 |
| 12 | whir-ud-goldilocks2-t128-rate1over16-d8-e1-l0-i4-k4-quadratic7 | 8 | 48368 | 552 | 81696 | 1318304 |
| 13 | whir-ud-goldilocks2-t100-rate1over2-d12-e1-l0-i4-k4-quadratic7 | 12 | 79936 | 1023 | 151404 | 1248596 |
| 14 | whir-ud-goldilocks2-t100-rate1over4-d12-e1-l0-i4-k4-ascending | 12 | 75232 | 1079 | 159692 | 1240308 |
| 15 | whir-ud-goldilocks2-t128-rate1over2-d12-e1-l1-i4-k4-ascending | 12 | 103584 | 1210 | 179080 | 1220920 |
| 16 | whir-ud-goldilocks2-t128-rate1over4-d12-e1-l1-i4-k4-affine3x5 | 12 | 97344 | 1337 | 197876 | 1202124 |
| 17 | whir-ud-goldilocks2-t100-rate1over16-d12-e1-l0-i4-k4-quadratic7 | 12 | 83776 | 1448 | 214304 | 1185696 |
| 18 | whir-ud-goldilocks2-t128-rate1over16-d12-e1-l1-i4-k4-ascending | 12 | 109472 | 1852 | 274096 | 1125904 |
| 19 | whir-ud-goldilocks2-t100-rate1over4-d18-e1-l0-i4-k4-affine3x5 | 18 | 163680 | 3376 | 499648 | 900352 |
| 20 | whir-ud-goldilocks2-t100-rate1over2-d18-e1-l0-i4-k4-affine3x5 | 18 | 175520 | 3571 | 528508 | 871492 |
| 21 | whir-ud-goldilocks2-t128-rate1over4-d18-e1-l0-i4-k4-affine3x5 | 18 | 213904 | 4358 | 644984 | 755016 |
| 22 | whir-ud-goldilocks2-t128-rate1over2-d18-e1-l0-i4-k4-affine3x5 | 18 | 227792 | 4552 | 673696 | 726304 |

## Compilation Blockers

- error: failed to download `indexmap v2.14.0`
- failed to parse manifest at `/Users/dominic/.cargo/registry/src/index.crates.io-6f17d22bba15001f/indexmap-2.14.0/Cargo.toml`
