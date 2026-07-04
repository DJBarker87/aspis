# WHIR-UD Reference Evaluation

## Scope

This is the Phase 1 reference evaluation for the fallback WHIR-UD spike. The goal here is only to answer:

1. Is there a buildable upstream `WizardOfMenlo/whir` reference?
2. Does it expose WHIR-UD explicitly enough to target it, rather than silently drifting into WHIR-JB/WHIR-CB?
3. What is the real configuration surface of the current code, as opposed to the paper/README surface?

No mirror verifier work starts from this document.

## Buildable Commit

- Repository: `https://github.com/WizardOfMenlo/whir`
- Buildable commit: `0aeaa7f337c743d9ddfcb9d909628d6491e3355c`
- Status: this commit is the current remote `HEAD` as observed on `2026-04-20`
- Local clone used: `/tmp/whir-ref`
- Local state: clean
- Package `rust-version`: `1.87.0`
- Built successfully with local `rustc 1.93.0 (254b59607 2026-01-19)`

Build verification:

- `cargo run --release --manifest-path /tmp/whir-ref/Cargo.toml -- --help`
- Raw output: `results/whir-ud-spike/raw/reference/help.txt`

## Current CLI Surface vs README

The current binary interface does **not** match the README.

README still advertises:

- `--type`
- `--sec`
- `--fold_type`
- default field `Goldilocks2`

Current `--help` at commit `0aeaa7f...` exposes:

- `--security-level`
- `--pow-bits`
- `--num-variables`
- `--evaluations`
- `--linear-constraints`
- `--rate`
- `--initfold`
- `--fold`
- `--unique-decoding`
- `--field`
- `--hash`
- `--zk`

And the current defaults are:

- field: `Goldilocks3`
- hash: `Blake3`
- security level: `128`

This matters because the old README phrasing suggests a clean `--sec` soundness-mode switch, but the current code has changed shape.

## How WHIR-UD Is Selected

WHIR-UD is exposed explicitly enough to target it.

Current path:

- `src/bin/main.rs`: CLI flag `--unique-decoding`
- `src/parameters.rs`: `ProtocolParameters { unique_decoding: bool, ... }`
- `src/protocols/whir/config.rs`: `Config::new(...)` threads `unique_decoding` into the initial IRS commitment and every subsequent round
- `src/protocols/irs_commit.rs`: `Config::new(...)` sets:
  - `johnson_slack = 0.0`
  - `out_domain_samples = 0`
  when `unique_decoding == true`

Structural check:

- `src/protocols/irs_commit.rs`: `unique_decoding()` is true exactly when `out_domain_samples == 0` and `johnson_slack == 0.0`
- `src/protocols/whir/config.rs`: `Config::unique_decoding()` requires the initial committer and all round committers to satisfy that predicate

That is a clean-enough separation for the PCS path:

- `--unique-decoding` => unique-decoding IRS configuration in every WHIR round
- no `--unique-decoding` => list-decoding regime with Johnson slack and OOD samples

Important nuance:

- current binary no longer exposes a top-level `--type PCS|LDT`
- instead, the PCS binary behaves like an LDT when `num_evaluations + num_linear_constraints == 0`
- the CLI comment says “LDT is always UD”

Conclusion: the current reference **does** expose WHIR-UD explicitly enough for a WHIR-UD-only spike.

## Configuration Axes

### Field choice

Exposed in `src/cmdline_utils.rs`:

- `Goldilocks1`
- `Goldilocks2`
- `Goldilocks3`
- `Field128`
- `Field192`
- `Field256`

Important distinction for PCS:

- `Goldilocks1` uses `Identity<Field64>`: source field and target field are both 64-bit Goldilocks
- `Goldilocks2` uses `Basefield<Field64_2>`: source field is 64-bit Goldilocks, target field is a quadratic extension
- `Goldilocks3` uses `Basefield<Field64_3>`: source field is 64-bit Goldilocks, target field is a cubic extension

So the codebase’s practical “Goldilocks” modes are not all the same thing:

- `Goldilocks1` = pure 64-bit field
- `Goldilocks2` = Goldilocks base field with 128-bit extension target
- `Goldilocks3` = Goldilocks base field with 192-bit extension target

The current binary default is `Goldilocks3`, not `Goldilocks1`.

### Security level

Exposed directly as `--security-level <usize>`.

The code computes soundness per round from the chosen field size, rate, folding schedule, and PoW. It does not expose separate WHIR-JB/WHIR-CB labels in the CLI anymore. The live switch is:

- `--unique-decoding` on/off

### Rate

Exposed as `--rate <RATE>`.

This is `starting_log_inv_rate`:

- `1` => rate `1/2`
- `2` => rate `1/4`
- `3` => rate `1/8`
- `4` => rate `1/16`

The code is generic over `usize`; the user-facing meaningful range is the expected power-of-two inverse-rate family.

### Folding parameter

Exposed as:

- `--initfold`
- `--fold`

Current defaults:

- `--initfold 4`
- `--fold 4`

The paper’s reported parameter choices line up with `k = 4`, but the current implementation is not hard-coded to 4. Tests in `src/protocols/whir/mod.rs` exercise smaller values as well.

Practical note: for the theorem-backed WHIR-UD comparison, keeping `k = 4` is the conservative choice unless there is a very good reason to deviate.

### Trace size / number of variables

Exposed as `--num-variables <NUM_VARIABLES>`.

The committed vector size is `2^num_variables`.

Structural limitation:

- `src/protocols/irs_commit.rs` requires `vector_size.is_multiple_of(interleaving_depth)`
- `interleaving_depth = 2^initial_folding_factor`

So with the default `--initfold 4`, the smallest meaningful trace size is:

- `num_variables >= 4`

Observed:

- `d = 3`, `initfold = 4` panics immediately
- raw output: `results/whir-ud-spike/raw/reference/goldilocks1-ud-d3-invalid.txt`

### Hash function

Exposed as `--hash`:

- `Blake3`
- `Sha3`
- `Keccak`
- `Sha2`

But that is **not** the whole transcript story.

What `--hash` controls:

- matrix-commit leaf hashing
- Merkle hashing
- PoW engine hashing

What it does **not** control:

- the standard transcript duplex hash, which uses `spongefish::StdHash`
- at the pinned spongefish revision, `StdHash = Shake128`
- protocol/session domain-separator hashing uses `Sha3_512` / `Sha3_256`

So the current upstream split is:

- Merkle / PoW: CLI-selectable hash engine
- transcript duplex: fixed `Shake128`
- protocol/session domain separators: fixed SHA3

That means the paper-level intuition “Blake3 for Merkle, SHA3 for Fiat-Shamir” is only approximately true for the current code. The real transcript path is mixed.

### PoW / grinding bits

Exposed as `--pow-bits`.

This is a real knob, but it is not a hard cap on the actual round PoW difficulty.

Current behavior:

- `ProtocolParameters.pow_bits` reduces the non-PoW security target used when building the round configs
- actual round-specific PoW bits are then recomputed from the soundness equations
- `Config::check_max_pow_bits(...)` only warns if a round needs more than the requested maximum
- proof generation still proceeds with the larger internally computed difficulty

Structural limitation:

- `src/protocols/proof_of_work.rs` asserts difficulty is within `[0, 60]`
- upstream spongefish Blake3 PoW implementation also asserts `< 60`

Observed practical failure:

- non-UD Goldilocks1 at `l=100, d=8, r=1, i=4, k=4` panics because required PoW exceeds the supported bound
- raw output: `results/whir-ud-spike/raw/reference/goldilocks1-list-d8-panic.txt`

This is a real Phase 2 risk, not just a cosmetic mismatch.

## Practical Reachability Probes

These are not the full Phase 2 matrix. They are only sanity probes to establish what the current reference can run today.

### WHIR-UD, Goldilocks2, tiny PCS sanity

Command:

- `cargo run --release --manifest-path /tmp/whir-ref/Cargo.toml -- --unique-decoding -l 100 -d 4 -e 1 -r 1 -i 4 -k 4 -f Goldilocks2 --hash Blake3 --reps 1`

Observed:

- source field: 64-bit Goldilocks
- target field: 128-bit extension
- proof size: `24.3 KiB`
- verifier hashes: `0.2k`
- verifier time: `6.6ms`

Raw output:

- `results/whir-ud-spike/raw/reference/goldilocks2-ud-d4.txt`

### WHIR-UD, Goldilocks3, tiny PCS sanity

Command:

- `cargo run --release --manifest-path /tmp/whir-ref/Cargo.toml -- --unique-decoding -l 100 -d 4 -e 1 -r 1 -i 4 -k 4 -f Goldilocks3 --hash Blake3 --reps 1`

Observed:

- source field: 64-bit Goldilocks
- target field: 192-bit extension
- proof size: `24.4 KiB`
- verifier hashes: `0.2k`
- verifier time: `9.5ms`

Raw output:

- `results/whir-ud-spike/raw/reference/goldilocks3-ud-d4.txt`

### WHIR-UD, Field192, tiny PCS sanity

Command:

- `cargo run --release --manifest-path /tmp/whir-ref/Cargo.toml -- --unique-decoding -l 100 -d 4 -e 1 -r 1 -i 4 -k 4 -f Field192 --hash Blake3 --reps 1`

Observed:

- proof size: `72.6 KiB`
- verifier hashes: `0.2k`

Raw output:

- `results/whir-ud-spike/raw/reference/field192-ud-d4.txt`

### Goldilocks1 practical warning

Pure `Goldilocks1` is exposed, but at 100-bit settings it already looks problematic:

- WHIR-UD, `d=4`, `rate=1/2`, `k=4` requires `37.0` bits of initial sumcheck PoW and `19.9` bits final PoW
- the code only warns if that exceeds the requested `--pow-bits`; it does not clamp it
- in practice that makes even tiny runs unattractive for Phase 2 host exploration

This does **not** make the reference unusable, but it does mean the phrase “Goldilocks field” needs to be interpreted carefully:

- if it means pure 64-bit `Goldilocks1`, Phase 2 may hit PoW and security pathologies very quickly
- if it means Goldilocks-base PCS with extension target field, `Goldilocks2`/`Goldilocks3` are the practical upstream modes

## Proof Format / Mirror-Verifier Feasibility

Upstream proof object:

- `src/transcript/mod.rs`
- `pub struct Proof { pub narg_string: Vec<u8>, pub hints: Vec<u8>, ... }`
- derives `Serialize` and `Deserialize`

Implication:

- there is a concrete byte-carrying proof object
- the exact proof bytes are parseable in principle
- the current CLI does not export them to disk; it only reports aggregate proof size

So Phase 2 would need a small harness around the library API to emit the exact upstream `Proof` bytes, but this does **not** look like a protocol-format blocker.

## Phase 1 Conclusion

Phase 1 does **not** justify a fast RED by itself.

Findings:

1. The current upstream `WizardOfMenlo/whir` reference is buildable at `0aeaa7f337c743d9ddfcb9d909628d6491e3355c`.
2. WHIR-UD is exposed explicitly enough to target via `--unique-decoding`.
3. The README is stale; the current CLI surface is the code in `src/bin/main.rs`, not the README examples.
4. The real field story is broader than “Goldilocks”: the practical upstream PCS modes are `Goldilocks2` and `Goldilocks3`, while pure `Goldilocks1` looks fragile at 100-bit settings.
5. Proofs have an exact serializable object representation, so a byte-level mirror verifier remains plausible.
6. The largest early blocker is PoW handling: the code warns about requested `--pow-bits` being too small, but then still uses larger internally derived PoW difficulties, and the PoW implementation hard-limits difficulty to about 60 bits.

Recommendation before Phase 2:

- Proceed only after confirming the intended WHIR-UD field mode:
  - `Goldilocks1` (pure 64-bit target field), or
  - `Goldilocks2` / `Goldilocks3` (Goldilocks base field with extension target field)

My recommendation is to treat `Goldilocks2` and `Goldilocks3` as the practical upstream WHIR-UD reference modes, and to record `Goldilocks1` as an exposed but likely impractical corner for 100/128-bit theorem-backed settings.
