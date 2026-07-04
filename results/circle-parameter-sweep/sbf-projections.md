# Circle SBF projections

Generated: 2026-04-20T08:40:26.739242+00:00

Compilation status: `projection-only`.

## Methodology

Reuse the existing phase1 SVM cost model. For each successful host proof, derive feature counts from proof structure (hash calls/bytes, Merkle levels, field ops, staged upload bytes), then score with the chosen monolithic/core/transport models. This is a projection, not a direct SBF run.

## Blockers

- Pinned reference still inherits the earlier cargo-build-sbf blocker: Solana's bundled Cargo 1.84 rejects edition2024 crates in the dependency tree.
- To preserve proof-byte compatibility with the validated p3-circle reference commit, this sweep does not pin an older upstream version just to satisfy cargo-build-sbf.

## Ranked configurations

| rank | id | target | proof_bytes | projected_cu | budget_fraction | core_cu | transport_cu | dominant drivers |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `1` | `counter4-t100-rate1over2-q84-pow16-arity1` | `100` | `43149` | `12144181` | `8.67` | `12090938` | `49819` | extension_mul_ops=6668453, field_inv_ops=2851359, field_mul_ops=1077092 |
| `2` | `counter4-t100-rate1over2-q84-pow16-arity2` | `100` | `43149` | `12144181` | `8.67` | `12090938` | `49819` | extension_mul_ops=6668453, field_inv_ops=2851359, field_mul_ops=1077092 |
| `3` | `counter4-t100-rate1over2-q84-pow16-arity3` | `100` | `43149` | `12144181` | `8.67` | `12090938` | `49819` | extension_mul_ops=6668453, field_inv_ops=2851359, field_mul_ops=1077092 |
| `4` | `counter4-t100-rate1over2-q84-pow16-arity1-final2` | `100` | `43149` | `12144181` | `8.67` | `12090938` | `49819` | extension_mul_ops=6668453, field_inv_ops=2851359, field_mul_ops=1077092 |
| `5` | `counter4-t100-rate1over2-q84-pow16-arity1-commitpow8` | `100` | `43149` | `12144181` | `8.67` | `12090938` | `49819` | extension_mul_ops=6668453, field_inv_ops=2851359, field_mul_ops=1077092 |
| `6` | `counter4-t100-rate1over2-q92-pow8-arity1` | `100` | `47234` | `13256089` | `9.47` | `13197841` | `54460` | extension_mul_ops=7303544, field_inv_ops=3121843, field_mul_ops=1179297 |
| `7` | `counter4-t100-rate1over2-q92-pow8-arity2` | `100` | `47234` | `13256089` | `9.47` | `13197841` | `54460` | extension_mul_ops=7303544, field_inv_ops=3121843, field_mul_ops=1179297 |
| `8` | `counter4-t100-rate1over2-q92-pow8-arity3` | `100` | `47234` | `13256089` | `9.47` | `13197841` | `54460` | extension_mul_ops=7303544, field_inv_ops=3121843, field_mul_ops=1179297 |
| `9` | `counter4-t120-rate1over2-q104-pow16-arity1` | `120` | `53358` | `14923920` | `10.66` | `14858167` | `61419` | extension_mul_ops=8256180, field_inv_ops=3527570, field_mul_ops=1332606 |
| `10` | `counter4-t120-rate1over2-q104-pow16-arity2` | `120` | `53358` | `14923920` | `10.66` | `14858167` | `61419` | extension_mul_ops=8256180, field_inv_ops=3527570, field_mul_ops=1332606 |
| `11` | `counter4-t120-rate1over2-q104-pow16-arity3` | `120` | `53358` | `14923920` | `10.66` | `14858167` | `61419` | extension_mul_ops=8256180, field_inv_ops=3527570, field_mul_ops=1332606 |
| `12` | `counter4-t120-rate1over2-q112-pow8-arity1` | `120` | `57437` | `16035776` | `11.45` | `15965022` | `66055` | extension_mul_ops=8891270, field_inv_ops=3798055, field_mul_ops=1434812 |
| `13` | `counter4-t120-rate1over2-q112-pow8-arity2` | `120` | `57437` | `16035776` | `11.45` | `15965022` | `66055` | extension_mul_ops=8891270, field_inv_ops=3798055, field_mul_ops=1434812 |
| `14` | `counter4-t120-rate1over2-q112-pow8-arity3` | `120` | `57437` | `16035776` | `11.45` | `15965022` | `66055` | extension_mul_ops=8891270, field_inv_ops=3798055, field_mul_ops=1434812 |
| `15` | `counter4-t128-rate1over2-q112-pow16-arity1` | `128` | `57443` | `16035828` | `11.45` | `15965070` | `66060` | extension_mul_ops=8891270, field_inv_ops=3798055, field_mul_ops=1434812 |
| `16` | `counter4-t128-rate1over2-q112-pow16-arity2` | `128` | `57443` | `16035828` | `11.45` | `15965070` | `66060` | extension_mul_ops=8891270, field_inv_ops=3798055, field_mul_ops=1434812 |
| `17` | `counter4-t128-rate1over2-q112-pow16-arity3` | `128` | `57443` | `16035828` | `11.45` | `15965070` | `66060` | extension_mul_ops=8891270, field_inv_ops=3798055, field_mul_ops=1434812 |
| `18` | `counter4-t128-rate1over2-q120-pow8-arity1` | `128` | `61515` | `17147623` | `12.25` | `17071870` | `70690` | extension_mul_ops=9526361, field_inv_ops=4068539, field_mul_ops=1537018 |
| `19` | `counter4-t128-rate1over2-q120-pow8-arity2` | `128` | `61515` | `17147623` | `12.25` | `17071870` | `70690` | extension_mul_ops=9526361, field_inv_ops=4068539, field_mul_ops=1537018 |
| `20` | `counter4-t128-rate1over2-q120-pow8-arity3` | `128` | `61515` | `17147623` | `12.25` | `17071870` | `70690` | extension_mul_ops=9526361, field_inv_ops=4068539, field_mul_ops=1537018 |
