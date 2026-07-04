# Circle host roundtrip

Generated: 2026-04-20T08:17:59.535773+00:00

Reference: `uni_stark_circle_v1.postcard` at `0f87f2b543a01880274965c410bf804c124f5046` using M31 / Keccak256.

## Parameters

- `log_blowup=1` `log_final_poly_len=0` `max_log_arity=1` `num_queries=40` `query_pow_bits=8`

## Results

### Fibonacci8

- Trace rows: `8` width: `2` constraints: `5` public values: `3` max degree: `2`
- Proof bytes: `29363` sha256: `6fca7489f4f693b14b86b48d74e875461c10a318bf547498013e9c5ec13c4b31`
- Structure: degree_bits=`3` quotient_chunks=`1` fri_queries=`40` fri_rounds=`3` total_merkle_siblings=`760`
- Valid proof: reference=`accept` mirror=`accept`
- Mutations:
  - `query-response-bit` reference=`reject` mirror=`reject` matched=`true`
  - `merkle-path-bit` reference=`reject` mirror=`reject` matched=`true`
  - `transcript-commitment-bit` reference=`reject` mirror=`reject` matched=`true`
  - `final-polynomial-bit` reference=`reject` mirror=`reject` matched=`true`

### Square8

- Trace rows: `8` width: `1` constraints: `3` public values: `2` max degree: `3`
- Proof bytes: `22066` sha256: `10333a30e685d5b349c646bf3c851671f74cfe7ad4aa8a80a52f9a08688c3c33`
- Structure: degree_bits=`3` quotient_chunks=`2` fri_queries=`40` fri_rounds=`2` total_merkle_siblings=`560`
- Valid proof: reference=`accept` mirror=`accept`
- Mutations:
  - `query-response-bit` reference=`reject` mirror=`reject` matched=`true`
  - `merkle-path-bit` reference=`reject` mirror=`reject` matched=`true`
  - `transcript-commitment-bit` reference=`reject` mirror=`reject` matched=`true`
  - `final-polynomial-bit` reference=`reject` mirror=`reject` matched=`true`

### AffinePair16

- Trace rows: `16` width: `2` constraints: `6` public values: `4` max degree: `2`
- Proof bytes: `39028` sha256: `668932b700f04246488cc8dc2894be3ee677da687a25175cb0cbc37d3820f2f3`
- Structure: degree_bits=`4` quotient_chunks=`1` fri_queries=`40` fri_rounds=`4` total_merkle_siblings=`1040`
- Valid proof: reference=`accept` mirror=`accept`
- Mutations:
  - `query-response-bit` reference=`reject` mirror=`reject` matched=`true`
  - `merkle-path-bit` reference=`reject` mirror=`reject` matched=`true`
  - `transcript-commitment-bit` reference=`reject` mirror=`reject` matched=`true`
  - `final-polynomial-bit` reference=`reject` mirror=`reject` matched=`true`

## Divergences

None.
