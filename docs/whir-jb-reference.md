# WHIR-JB Reference Evaluation

## Scope

This is the Phase 1 reference evaluation for the WHIR-JB pivot. The goal here is only to answer:

1. Whether the pinned upstream `WizardOfMenlo/whir` reference cleanly exposes the Johnson-bound regime.
2. What the practical WHIR-JB configuration surface looks like at that commit.
3. Whether the requested sanity probes look good enough to justify Phase 2 mirror-verifier work.

No mirror verifier work starts from this document.

## Buildable Reference

- Repository: `https://github.com/WizardOfMenlo/whir`
- Pinned commit: `0aeaa7f337c743d9ddfcb9d909628d6491e3355c`
- Local clone used: `/tmp/whir-ref`
- Local state: clean
- Build check: `cargo run --release --manifest-path /tmp/whir-ref/Cargo.toml -- --help`
- Raw help output: `results/whir-jb-spike/raw/reference/help.txt`

## WHIR-JB Selection

### What selects JB

At this commit there is no explicit `--johnson-bound` flag. The regime selector is the inverse of `--unique-decoding`.

Relevant source paths:

- `src/bin/main.rs:51-56`
- `src/bin/main.rs:123-145`
- `src/parameters.rs:9-25`
- `src/protocols/whir/config.rs:40-48`
- `src/protocols/whir/config.rs:80-88`
- `src/protocols/whir/config.rs:154-160`
- `src/protocols/irs_commit.rs:145-201`
- `src/protocols/irs_commit.rs:244-255`

Observed behavior:

- `--unique-decoding` present => UD path.
- `--unique-decoding` absent => list-decoding path with Johnson slack and nonzero OOD samples.

This is clean enough to target WHIR-JB specifically. I did **not** find a third exposed regime mixed into the current CLI/config path. The current split is binary:

- UD
- non-UD list decoding with Johnson-bound slack

I did **not** find a separate capacity-bound selector in the pinned upstream code.

### Is JB the default?

Yes.

`src/bin/main.rs:51-56` defines `unique_decoding: bool` with `default_value_t = false`, so the default PCS regime is the non-UD branch. The current default field is `Goldilocks3`, not `Goldilocks2`.

### Johnson slack used by the reference

The reference uses the paper's Johnson slack choice:

- `η = sqrt(rate) / 20`

Source:

- `src/protocols/irs_commit.rs:144-151`

That is exactly the code path taken when `unique_decoding == false`.

### OOD samples used by JB

JB uses nonzero OOD samples, derived from the Johnson list-size term and field size:

- `src/protocols/irs_commit.rs:152-169`

For the practical runs below this was:

- usually `1` OOD sample per IRS commitment for Goldilocks3
- `1` for Goldilocks2 at 100-bit settings
- `2` already at `Goldilocks2, 128-bit, rate 1/2, d=16`

UD remains the `out_domain_samples = 0` case.

### How to verify the regime was selected

There are two reliable checks.

1. Source-level invariant:
   - `src/protocols/irs_commit.rs:244-255`
   - `unique_decoding()` is true exactly when `out_domain_samples == 0` and `johnson_slack == 0.0`.
2. Runtime output from the upstream CLI:
   - stdout prints `Security level: ... using list decoding`
   - each IRS commitment line prints nonzero `out-domain` samples for JB

Completed probe outputs showing this:

- `results/whir-jb-spike/raw/reference/jb-goldilocks3-t128-rate1over2-d20-i4-k4.txt`
- `results/whir-jb-spike/raw/reference/jb-goldilocks3-t100-rate1over16-d18-i4-k4.txt`

## Configuration Surface

### Field modes exposed with JB

The CLI exposes six field selections:

- `Goldilocks1`
- `Goldilocks2`
- `Goldilocks3`
- `Field128`
- `Field192`
- `Field256`

Source:

- `src/cmdline_utils.rs:7-30`
- `src/bin/main.rs:75-90`

Dispatch semantics:

- `Goldilocks1` => pure 64-bit Goldilocks via `Identity<Field64>`
- `Goldilocks2` => Goldilocks base field with quadratic extension target via `Basefield<Field64_2>`
- `Goldilocks3` => Goldilocks base field with cubic extension target via `Basefield<Field64_3>`
- `Field128` / `Field192` / `Field256` => prime-field identity embeddings

Tiny JB proof sanity at `l=100, d=4, r=1, i=4, k=4, e=1, hash=Blake3`:

| Field | Status | Proof size | Avg hashes | Raw output |
| --- | --- | ---: | ---: | --- |
| `Goldilocks1` | panic | n/a | n/a | `results/whir-jb-spike/raw/reference/field-goldilocks1-tiny.txt` |
| `Goldilocks2` | ok | `23.6 KiB` | `0.2k` | `results/whir-jb-spike/raw/reference/field-goldilocks2-tiny.txt` |
| `Goldilocks3` | ok | `23.7 KiB` | `0.2k` | `results/whir-jb-spike/raw/reference/field-goldilocks3-tiny.txt` |
| `Field128` | ok | `47.0 KiB` | `0.2k` | `results/whir-jb-spike/raw/reference/field-field128-tiny.txt` |
| `Field192` | ok | `70.4 KiB` | `0.2k` | `results/whir-jb-spike/raw/reference/field-field192-tiny.txt` |
| `Field256` | ok | `93.9 KiB` | `0.2k` | `results/whir-jb-spike/raw/reference/field-field256-tiny.txt` |

Practical read:

- `Goldilocks2`, `Goldilocks3`, `Field128`, `Field192`, and `Field256` all work on the JB path.
- `Goldilocks1` is exposed but already fails at a tiny 100-bit JB setting because the derived PoW exceeds the upstream 60-bit cap.

### Rates that work with JB

The CLI rate parameter is `starting_log_inv_rate`:

- `1` => rate `1/2`
- `2` => rate `1/4`
- `3` => rate `1/8`
- `4` => rate `1/16`

Source:

- `src/bin/main.rs:39-49`
- `src/parameters.rs:12-21`
- `src/protocols/whir/config.rs:36-48`

Tiny Goldilocks2 JB proofs completed for all four expected rates:

| Rate arg | Nominal rate | Proof size | Avg hashes | Raw output |
| --- | --- | ---: | ---: | --- |
| `1` | `1/2` | `23.6 KiB` | `0.2k` | `results/whir-jb-spike/raw/reference/field-goldilocks2-tiny.txt` |
| `2` | `1/4` | `11.1 KiB` | `0.1k` | `results/whir-jb-spike/raw/reference/rate-goldilocks2-tiny-r2.txt` |
| `3` | `1/8` | `7.2 KiB` | `0.1k` | `results/whir-jb-spike/raw/reference/rate-goldilocks2-tiny-r3.txt` |
| `4` | `1/16` | `5.6 KiB` | `0.1k` | `results/whir-jb-spike/raw/reference/rate-goldilocks2-tiny-r4.txt` |

### initfold / fold defaults

Defaults are:

- `--initfold 4`
- `--fold 4`

Source:

- `src/bin/main.rs:45-49`

I did not find any JB-specific override. The same folding defaults are used for both UD and non-UD, and `src/protocols/whir/config.rs:40-48` / `80-88` thread the supplied values through the same way regardless of regime.

Inference from the code and paper alignment:

- `4/4` remains the faithful default for JB at this commit.
- I found no source-level evidence that upstream prefers a different folding schedule for JB than for UD.

### JB defaults that differ from UD

The top-level CLI defaults do **not** change when JB is active. What changes is the derived IRS configuration:

- JB: `johnson_slack = sqrt(rate)/20`, nonzero OOD samples, list-decoding soundness accounting.
- UD: `johnson_slack = 0`, `out_domain_samples = 0`.

So the user-facing defaults are shared, but the effective round/query schedule is materially different once `--unique-decoding` is absent.

## Practical `num_variables` Range vs the 60-bit PoW Ceiling

The upstream PoW implementation hard-asserts the difficulty range `[0, 60]`:

- `src/protocols/proof_of_work.rs:29-39`

To sweep this efficiently I used a throwaway local helper linked directly against `/tmp/whir-ref` and calling the same upstream `whir::protocols::whir::Config::new` path without proving. This does **not** change the reference; it just queries the derived schedule from the pinned code. Raw sweep:

- `results/whir-jb-spike/raw/reference/config-sweep.tsv`

Tested range:

- `num_variables ∈ {16, 18, 20, 22, 24}`
- `initfold = 4`
- `fold = 4`
- default `pow_bits = 20`

Summary:

- `Goldilocks2`, 100-bit:
  - `rate 1/2`, `1/4`, `1/8` stayed under the 60-bit ceiling through `d=24`.
  - `rate 1/16` stayed under the ceiling through `d=22`; `d=24` panicked.
- `Goldilocks2`, 128-bit:
  - only `rate 1/2, d=16` fit under the 60-bit ceiling in the tested range (`max_pow_bits ≈ 58.25`)
  - `rate 1/2, d>=18` panicked
  - `rate 1/4`, `1/8`, `1/16` already panicked at `d=16`
- `Goldilocks3`, 100-bit and 128-bit:
  - every tested point in the `d=16..24`, `rate 1/2..1/16` grid stayed under the ceiling
  - observed `max_pow_bits` stayed roughly in the `19-26` bit range

This is the central Phase 1 result for configuration space:

- `Goldilocks2` is not a practical 128-bit JB field at meaningful trace sizes in the current upstream reference.
- `Goldilocks3` is the practical 128-bit JB field in the current upstream reference.

## Requested Sanity Probes

### Target probe outcomes

These were run as PCS proofs with `-e 1`, `hash=Blake3`, and default `pow_bits=20` unless noted otherwise.

| Requested config | Status | Proof size | Avg hashes | Notes | Raw output |
| --- | --- | ---: | ---: | --- | --- |
| JB, `Goldilocks2`, 100-bit, `rate 1/2`, `d=18`, `i=4`, `k=4` | did not complete | n/a | n/a | upstream prove was allowed to run for `12m21s` and was still grinding; schedule-only config reports `max_pow_bits = 34.25` | `results/whir-jb-spike/raw/reference/jb-goldilocks2-t100-rate1over2-d18-i4-k4.txt`, `results/whir-jb-spike/raw/reference/jb-goldilocks2-t100-rate1over2-d18-i4-k4-config.json` |
| JB, `Goldilocks2`, 100-bit, `rate 1/4`, `d=18`, `i=4`, `k=4` | did not complete | n/a | n/a | schedule printed, then aborted after `20s`; config-only sweep shows `max_pow_bits = 37.75`, worse than the already-stalled `rate 1/2` case | `results/whir-jb-spike/raw/reference/jb-goldilocks2-t100-rate1over4-d18-i4-k4.txt`, `results/whir-jb-spike/raw/reference/jb-goldilocks2-t100-rate1over4-d18-i4-k4-config.json` |
| JB, `Goldilocks2`, 128-bit, `rate 1/2`, `d=18`, `i=4`, `k=4` | panic | n/a | n/a | config creation hit the upstream `>60` bit PoW assertion | `results/whir-jb-spike/raw/reference/jb-goldilocks2-t128-rate1over2-d18-i4-k4.txt`, `results/whir-jb-spike/raw/reference/jb-goldilocks2-t128-rate1over2-d18-i4-k4-config.json` |
| JB, `Goldilocks2`, 128-bit, `rate 1/2`, `d=20`, `i=4`, `k=4` | panic | n/a | n/a | config creation hit the upstream `>60` bit PoW assertion | `results/whir-jb-spike/raw/reference/jb-goldilocks2-t128-rate1over2-d20-i4-k4.txt`, `results/whir-jb-spike/raw/reference/jb-goldilocks2-t128-rate1over2-d20-i4-k4-config.json` |
| JB, `Goldilocks3`, 128-bit, `rate 1/2`, `d=20`, `i=4`, `k=4` | ok | `180.5 KiB` | `4.0k` | completed in `842.9ms`; this is already far above the hoped-for `10-30 KiB` band | `results/whir-jb-spike/raw/reference/jb-goldilocks3-t128-rate1over2-d20-i4-k4.txt`, `results/whir-jb-spike/raw/reference/jb-goldilocks3-t128-rate1over2-d20-i4-k4-config.json` |

### Supplemental viable-branch probes

Because `Goldilocks3` is the only practical 128-bit branch in the current upstream schedule, I also ran additional completed probes there to see whether tighter rates get into the desired proof-size range.

128-bit, `Goldilocks3`, `d=20`, `i=4`, `k=4`:

| Rate | Proof size | Avg hashes | Raw output |
| --- | ---: | ---: | --- |
| `1/2` | `180.5 KiB` | `4.0k` | `results/whir-jb-spike/raw/reference/jb-goldilocks3-t128-rate1over2-d20-i4-k4.txt` |
| `1/4` | `129.4 KiB` | `2.8k` | `results/whir-jb-spike/raw/reference/jb-goldilocks3-t128-rate1over4-d20-i4-k4.txt` |
| `1/8` | `109.4 KiB` | `2.4k` | `results/whir-jb-spike/raw/reference/jb-goldilocks3-t128-rate1over8-d20-i4-k4.txt` |
| `1/16` | `96.9 KiB` | `2.1k` | `results/whir-jb-spike/raw/reference/jb-goldilocks3-t128-rate1over16-d20-i4-k4.txt` |

100-bit, `Goldilocks3`, `d=18`, `i=4`, `k=4`:

| Rate | Proof size | Avg hashes | Raw output |
| --- | ---: | ---: | --- |
| `1/2` | `113.9 KiB` | `2.4k` | `results/whir-jb-spike/raw/reference/jb-goldilocks3-t100-rate1over2-d18-i4-k4.txt` |
| `1/4` | `80.0 KiB` | `1.7k` | `results/whir-jb-spike/raw/reference/jb-goldilocks3-t100-rate1over4-d18-i4-k4.txt` |
| `1/8` | `68.2 KiB` | `1.4k` | `results/whir-jb-spike/raw/reference/jb-goldilocks3-t100-rate1over8-d18-i4-k4.txt` |
| `1/16` | `60.7 KiB` | `1.3k` | `results/whir-jb-spike/raw/reference/jb-goldilocks3-t100-rate1over16-d18-i4-k4.txt` |

## Phase 1 Readout

1. **JB exposure is clean enough to target.**
   The pinned reference exposes a binary regime switch: UD when `--unique-decoding` is present, Johnson/list-decoding when it is absent. I did not find a mixed or hidden capacity-bound branch in this path.

2. **`Goldilocks2` is not a practical 128-bit JB field in the pinned upstream reference.**
   At the requested 128-bit settings, moderate `Goldilocks2` points already hit the hard 60-bit PoW ceiling during schedule derivation.

3. **The viable 128-bit branch is `Goldilocks3`, and its proofs are already large.**
   The completed `Goldilocks3` 128-bit probes land around:
   - `96.9 KiB` at the most favorable completed `rate 1/16, d=20` point
   - `180.5 KiB` at `rate 1/2, d=20`
   with roughly `2.1k-4.0k` verifier hashes.

4. **This is already an early warning against Phase 2.**
   The prompt's "promising" band was roughly `10-30 KiB` proofs with `1-3k` hashes. The completed `Goldilocks3` probes are nowhere near that proof-size band, and the requested `Goldilocks2` 128-bit points are structurally blocked before proving.

5. **Phase 2 should not start yet.**
   Per instruction, I am stopping after Phase 1. My recommendation from this evidence is a **fast RED / strong stop signal** unless you explicitly want Phase 2 anyway despite:
   - `Goldilocks2` 128-bit moderate parameters failing the upstream PoW ceiling
   - `Goldilocks3` 128-bit moderate parameters producing `~97-181 KiB` proofs before any Solana port work
