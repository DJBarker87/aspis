# ML-DSA Solana STARK Stage B Projection Gate

Date of run: `2026-04-20`

Primary artifact:

- `results/mldsa-solana-stark/stage-b-projection.json`

Reproduction command:

```bash
experiments/mldsa-solana-stark/run-stage-b-projection.sh
```

## What Was Checked

This gate combined four things:

1. the already measured `ML-DSA-44` SHAKE transcript:
   - `ExpandA`
   - `tr`
   - `mu`
   - `ctilde'`
   - `SampleInBall`
2. a concrete `255`-column-compliant Keccak-f AIR candidate inside `Winterfell 0.12`
3. a row model for the arithmetic slice:
   - decode
   - `NTT`
   - matrix multiply
   - `UseHint`
   - `w1Encode`
   - norm check
4. a synthetic Winterfell proof proxy at the same trace width / trace length / proof options

## Verified Field-Surface Findings

- `Winterfell 0.12` exposes prime fields `f62`, `f64`, and `f128`.
- `f64` is the Goldilocks prime field with modulus `2^64 - 2^32 + 1`.
- `Winterfell 0.12` does **not** expose a binary-field backend in the checked source surface.
- The hard trace-width cap remains `255` columns.

## Exact Measured SHAKE Transcript

From the pinned Stage B artifacts:

- `ExpandA`: `80` permutations
- `tr`: `10` permutations
- `mu`: `1` permutation
- `ctilde'`: `7` permutations
- `SampleInBall`: `1` permutation

Exact total:

- `99` Keccak-f permutations

This matters because it keeps the combined exact trace under `2^19` rows after padding. The
earlier rough `120`-permutation envelope is still reported as a conservative side case, but it is
not the exact measured count for the pinned fixture.

## Keccak AIR Candidate

Chosen candidate:

- base field: `f64` Goldilocks
- trace width: `35`
- live trace columns:
  - `25` state bits
  - `5` theta `C[x]` bits
  - `5` theta `D[x]` bits
- fixed / periodic columns:
  - phase selector
  - round selector
  - bit-index selector
  - rho/pi mapping
  - iota round-constant bits

Round schedule:

- theta: `64` rows
- rho/pi: `64` rows
- chi+iota: `64` rows

Rows per permutation:

- `4608`

Resulting SHAKE rows:

- exact measured transcript: `99 * 4608 = 456,192`
- conservative `120`-permutation envelope: `552,960`

## Arithmetic Slice Model

Modeled rows:

- total arithmetic rows: `29,696`

Largest modeled arithmetic width:

- `12` columns

So the full candidate is still Keccak-width dominated:

- max trace width: `35`

## Combined Trace Projection

Exact measured transcript case:

- total active rows: `485,888`
- padded trace length: `524,288`
- width: `35`

Conservative `120`-permutation case:

- total active rows: `582,656`
- padded trace length: `1,048,576`
- width: `35`

Main-trace query lower bounds alone:

- `f64`, `30` queries: `8,400` bytes
- `f128`, `30` queries: `16,800` bytes

This already says the f128 path is dead on width alone. The Goldilocks path is the only one even
worth proxying.

## Synthetic Winterfell Proof Proxy

Proxy configuration:

- field: `f64`
- extension: `Quadratic`
- width: `35`
- trace length: `524,288`
- proof options mirrored from the local Yano-derived prover:
  - `30` queries
  - blowup `16`
  - grinding `8`
  - FRI folding `4`
  - remainder degree `31`

Measured proxy result:

- proof bytes: `120,128`
- generation time: `32,549 ms`

Important caveat:

- the proxy used the available `SHA3_256` hasher from crates.io `Winterfell 0.12`, not the local
  patched `Sha2_256` surface in the vendored Yano-derived stack
- this matters for exact apples-to-apples parity, but it does **not** plausibly explain a gap from
  `~10 KB` target envelope to `~120 KB` measured proxy bytes

## Interpretation

This is no longer a speculative concern.

Under an explicit `35`-column Goldilocks Keccak candidate that respects the `255`-column cap:

- the exact measured `ML-DSA-44` SHAKE transcript plus arithmetic slice projects to a
  `524,288`-row trace
- a synthetic Winterfell proof at that shape is about `120 KB`

That is roughly:

- `11.9x` the `10,068`-byte staged payload envelope used in the pinned Yano transport note
- `~28.5x` the `4,211`-byte minimal local Yano-style proof artifact

## Gate Decision

`RED-STOP`

Reason:

- the exact measured Stage B candidate is not close to the target envelope
- even after:
  - switching from the pinned local `f128` field to Goldilocks `f64`
  - keeping trace width down to `35`
  - using the exact measured `99`-permutation transcript instead of the rougher `120` envelope
- the proof proxy is still `~120 KB`

## Bounded Negative Result

The current defensible negative claim is:

- `Within Winterfell 0.12, a 255-column-compliant Goldilocks-based Keccak AIR candidate for`
  `spec-faithful ML-DSA-44 verification on the measured transcript still projects to roughly`
  `120 KB proofs at the required trace scale, far above the Yano-style staged Solana envelope.`

What this does **not** claim:

- that no other STARK framework could do better
- that no more aggressive Keccak arithmetization exists
- that no protocol modifications could change the outcome

What it **does** claim:

- this pinned Winterfell-based path, under an explicit measured Stage B candidate, does not fit the
  project's bounded Solana envelope

## Consequence For Scope

Continuing to Stage C under the original framing would no longer be honest.

The remaining honest options are:

1. stop here and frame the work as a publishable Stage B negative result, or
2. explicitly change scope:
   - different proof system
   - different framework version
   - non-spec-compliant Dilithium-family modifications
   - different transport envelope

Any of those are real scope deviations and should be named as such.
