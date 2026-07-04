# ML-DSA Solana STARK Literature Scan

Date of scan: `2026-04-20`

This note is intentionally narrow. It only covers the framing question:

- is there already public prior work on `Dilithium` / `ML-DSA` inside a `STARK` or STARK-based stack?
- do the current first-party repos for `Risc0`, `SP1`, `Jolt`, or `Plonky3` expose public
  `Dilithium` / `ML-DSA` examples or benchmarks?

## Bottom Line

- I found one clearly relevant prior-work paper:
  - `Post-Quantum Privacy Pass via Post-Quantum Anonymous Credentials`
  - `ePrint 2023/414`
  - URL: `https://eprint.iacr.org/2023/414.pdf`
- That paper is relevant, but it does **not** collapse this project's framing into “already done.”
  - It uses `zkDilithium`, described in the paper as a `STARK-friendly variation on Dilithium2`
  - It is not a claim about exact `FIPS 204 ML-DSA.Verify_internal`
  - It is not Solana
  - It is not Winterfell
  - It is not an on-chain verifier study
- I did **not** find evidence, in the current public first-party repo heads of `Risc0`, `SP1`, `Jolt`,
  or `Plonky3`, of a first-party `Dilithium` / `ML-DSA` benchmark or AIR/example.
- That means the safe framing is:
  - there is relevant prior STARK-adjacent work on a Dilithium-family variant (`zkDilithium`)
  - I have not yet verified prior public work for exact `ML-DSA` verification in `Winterfell` or on Solana

## Relevant Prior Work Found

### ePrint 2023/414

Paper:

- `Post-Quantum Privacy Pass via Post-Quantum Anonymous Credentials`
- URL: `https://eprint.iacr.org/2023/414.pdf`

Relevant text from the paper:

- it presents `zkDilithium`, described as `a STARK-friendly variation on Dilithium2`
- it reports a proof-size / prover-time trade-off with:
  - token size `85-175 KB`
  - generation time `0.3-5 s`
  - proof security level `115 bits`
  - verification time `20-30 ms`

Why it matters:

- it is direct evidence that the Dilithium family has already been studied in a STARK-oriented setting
- it weakens any casual “first Dilithium in STARK” claim

Why it does **not** settle this project's framing:

- it is a modified `zkDilithium` construction, not exact `FIPS 204 ML-DSA`
- its application is anonymous credentials / Privacy Pass, not Solana on-chain verification
- it does not answer the Solana `1.4M` CU question

## Repo-Head Scan Results

The following scans were done against the current public repo heads from official GitHub repos or closely
associated benchmark repos. The query used was a case-insensitive text search for:

- `dilithium`
- `ml-dsa`
- `mldsa`

Scanned repos:

- `https://github.com/succinctlabs/sp1`
- `https://github.com/a16z/jolt`
- `https://github.com/Plonky3/Plonky3`
- `https://github.com/risc0/risc0`
- `https://github.com/succinctlabs/zkvm-perf`
- `https://github.com/babybear-labs/benchmark`
- `https://github.com/brevis-network/zkvm-bench`

Observed result:

- no direct keyword matches were found in the repo heads I scanned

What that does and does not mean:

- it lowers the probability that one of these projects already ships a first-party public Dilithium / ML-DSA
  example or benchmark
- it does **not** prove absence of all external projects built on top of these stacks
- it does **not** justify a “first” claim by itself

## Framing Update

The safest framing after this scan is:

- `This work measures exact FIPS 204 ML-DSA-44 verification encoded in a Winterfell 0.12 STARK and
  verified on Solana, while comparing against both the vendored Yano Solana baseline and relevant prior
  STARK-adjacent Dilithium-family work such as zkDilithium.`

The unsafe framing is:

- `first Dilithium in STARK`
- `first ML-DSA in zero knowledge`
- `state of the art`

Those still require a broader literature review before they can be said at all.
