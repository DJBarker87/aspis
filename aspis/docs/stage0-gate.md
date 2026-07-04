# Stage 0 gate note — substrate consolidation

Date: 2026-07-04. Base repo revision at Stage 0 start: `d0d7605`.
Design reference: `docs/aspis-staged-design.md`, section 7.
Audit reference: `docs/aspis-stage0-audit.md`.

## 1. Deviation record (named, per working rule §16)

**Deviation 1 — no pre-existing native v0 in this tree.** The design's Stage 0
work item 1 reads "port the winning Phase 2 configuration into native v0".
This repository (at `d0d7605`) was searched before any code was written; it
contains the Phase 1 cost-model scaffold, the Phase 2 skeleton-kernel
experiments, and the Phase 2 real-Winterfell measurements — but **no native
WHIR-M31 verifier, no 326,021 CU measurement, no 927,227 CU proxy freeze, no
852,745 CU best, no `round_batch_inversion` or `proof_carried_round_local`
implementation, and no whir-p3 cross-validation artifacts**. Those figures
exist only as context inside the design document and are not reproducible
from this tree. Stage 0 was therefore executed as: **bootstrap native v0 in a
fresh subrepo (`aspis/`) with the winning configuration built in from the
start**, rather than porting into an existing slice. Everything the port
list names is present by construction:

- `reference_canonical` M31 reduction (`aspis-core/src/field.rs`)
- Karatsuba CM31/QM31 multiplication + `late_lift_qm31` mixed-width kernels
- `raw_fibers` fold payload (default)
- `minimal_subtree` Merkle multiproof mode (and `single_paths` for the delta)
- `round_batch_inversion` (one batched inversion per fold round)
- `proof_carried_round_local` implemented behind a header flag and sized
  (work item 1's "evaluate against its proof-byte cost" — see §4)

**Deviation 2 — gate-focused on-chain matrix.** The full packaging matrix
(`stage0-onchain`) is intentionally slow because every corruption case is
uploaded as a separate proof account. The main artifact committed here was
produced by `stage0-onchain-gate`: minimal-subtree profiles only, covering
capacity lr12 raw/carried, Johnson q80 raw/carried, and the narrow-layout
lr14 diagnostic. The slow full matrix remains available for packaging deltas.
The gate result is decisive for two choices only: `proof_carried_round_local`
is out, and Johnson q80 is research-track under the current implementation.

**Deviation 3 — lr14 is demoted from target to diagnostic.** The original
Stage 0 gate treated `capacity_lr14_q40_g16` as "statement-sized". That was a
narrow-table sizing assumption, not a frozen statement layout. The wide-row
layout required by design item §13.8 trades rows for columns, so the true
statement target must be selected by a measured `(log_rows, k)` sweep before
Stage 0 is re-evaluated. The lr14 RED is preserved as useful data about a
bad table shape; it is not accepted as the bounded negative for Aspis.

## 2. Reconciliation note (work item 3)

The design asks for a one-page note reconciling "the proxy freeze, the later
Phase 2 measurements, and the new native numbers".

- **Proxy freeze (927,227 CU) / later proxy best (852,745 CU)**: these are
  present in the parent repo Phase 2 artifacts, not in the new native
  `aspis/` implementation. The frozen proxy summary
  (`../results/phase2/whir-m31-capacity-v0/summary.json`) reports 927,227 CU
  total / 914,591 CU verify for `whir_t128_capacity_full` with
  `raw_fibers + minimal_subtree`. The later proof-carried round-local proxy
  run (`../results/phase2/whir-roundlocal/summary.json`) reports 852,745 CU
  total / 839,893 CU verify with +312 proof bytes. Native measurement rejects
  that tradeoff: proof-carried costs +5,536 bytes and +15,535 CU at lr12.
  Therefore the proxy best is a historical diagnostic, not the native freeze.
- **Phase 2 measurements that ARE in this tree** (`results/phase2*`,
  regenerable via `cargo xtask phase2-experiments` at the repo root): kernel
  winners `reference_canonical` + `karatsuba` + `late_lift_qm31`; best
  skeleton variant measured at 667,770 CU total; higher-fidelity
  `whir_t100_capacity_full` evaluator at 458,043 CU; real-Winterfell trace-8
  at 1,157,699 CU with recursive variants hitting the 1.4M cap. These
  motivate the substrate choice and the kernel set, and nothing else.
- **Full-reuse proxy comparator**:
  `../results/phase2/whir-full-reuse/raw.jsonl` contains the closest proxy
  comparator to native raw/minimal/batch-inversion: 862,238 CU verify /
  874,724 CU total for `whir_t128_capacity_full`, 39 explicit queries, proof
  bytes 5,932. Its phase split was parse 1,486, transcript setup 19,425,
  OOD 12,144, per-round queries 770,128, folding 12,462, final round 49,043.
- **New native numbers**: host-side numbers are in
  `results/stage0/host_summary.json`; gate-focused SBF numbers are in
  `results/stage0/onchain_summary.json`. The capacity lr12 raw/minimal profile
  accepts at 1,063,093 CU on Agave 2.3.0. The native trace artifact
  `results/stage0/onchain_profile.json` attributes most of that cost to
  per-layer Merkle work plus folding checks: ~267,744 CU Merkle, ~733,692 CU
  fold, and ~71,841 CU setup/final/trace overhead. The native-vs-proxy gap is
  therefore primarily in the per-round verifier body, plus native uses q40/g16
  with five arity-4 rounds while the closest proxy used a two-bucket q39
  schedule and OOD accounting.
- **g32 diagnostic**: `results/stage0/onchain_g32_summary.json` shows that
  increasing grinding to 32 bits and reducing explicit queries is a material
  lever. `capacity_lr12_q36_g32` accepts at 1,025,729 CU; `q32_g32` accepts at
  894,891 CU. Both rejected all nine on-chain corruption cases. These are
  diagnostic profiles only until Stage 1 soundness accounting validates the
  query trade.
- **Layout diagnostic**: `results/stage0/layout_sweep.json` measures the
  first wide-row tradeoff. Merkle simulation cost decreases with `log_rows`,
  while the naive gamma-RLC loop grows linearly in columns. The corrected
  probe hashes one wide leaf per query. Combined with
  `results/stage0/onchain_layout_target_summary.json`, the measured target is
  lr10/k64/q32; lr6 with k=400 is already too RLC-heavy under the naive loop.

## 3. What v0 is, precisely

Committed object: evaluations of a polynomial of degree < 2^log_rows (M31
coefficients) over a coset of a 2^(log_rows+log_blowup) subgroup of the M31
circle group in CM31; leaves pack whole arity-4 fold fibers; SHA-256
throughout (syscall on-chain). Per round (fold_vars = 2): absorb root, sample
one QM31 challenge, fold x → x⁴ via two local pair-folds (challenges α, α²);
after all rounds the final 4 coefficients ship in the clear; grinding is
checked after the final-poly absorb; query positions are derived last and
each query is one leaf opening per layer plus local fold-consistency checks
down to the final polynomial. Statement binding: a 32-byte digest absorbed
before any commitment, plus the full header (profile id, sizes, packaging
flags) absorbed first — profile-swap and packaging-swap replays reject.

What v0 proves is **transcript-bound local fold consistency**, the same
characterization the design gives the reference native v0. It is not paper
WHIR: no OOD samples, no sumcheck/fold interleaving, no final-round degree
check beyond the explicit final polynomial, no externally supplied evaluation
claim. That delta is Stage 1's entire job (design §8.1 checklist).

## 4. Measured results (host, this environment)

Source: `results/stage0/host_summary.json`, generated 2026-07-04 by
`cargo run --release -p aspis-xtask -- stage0-host`. 10 proofs per variant,
distinct statements. All soundness labels: **heuristic** (Stage 1 pending);
the capacity/Johnson profile names denote query-count shapes only. This
artifact was regenerated after the upload-account authority hardening; proof
bytes are unchanged because that header lives in the staged upload account,
not inside the proof envelope.

| profile | payload | merkle | proof bytes (mean) | accept |
| --- | --- | --- | ---: | --- |
| capacity_lr12_q40_g16 | raw_fibers | minimal_subtree | 24,790 | 10/10 |
| capacity_lr12_q40_g16 | raw_fibers | single_paths | 54,060 | 10/10 |
| capacity_lr12_q40_g16 | carried | minimal_subtree | 30,172 | 10/10 |
| capacity_lr12_q40_g16 | carried | single_paths | 59,720 | 10/10 |
| johnson_lr12_q80_g16 | raw_fibers | minimal_subtree | 39,616 | 10/10 |
| johnson_lr12_q80_g16 | raw_fibers | single_paths | 99,839 | 10/10 |
| johnson_lr12_q80_g16 | carried | minimal_subtree | 48,681 | 10/10 |
| johnson_lr12_q80_g16 | carried | single_paths | 108,354 | 10/10 |
| capacity_lr14_q40_g16 | raw_fibers | minimal_subtree | 37,666 | 10/10 |
| capacity_lr14_q40_g16 | raw_fibers | single_paths | 74,945 | 10/10 |
| capacity_lr14_q40_g16 | carried | minimal_subtree | 44,076 | 10/10 |
| capacity_lr14_q40_g16 | carried | single_paths | 81,223 | 10/10 |

Observations recorded for the frozen-profile decision (design decision item 4):

- `minimal_subtree` cuts proof bytes ~2.2× at lr12/q40 and ~2.5× at q80
  versus independent paths. It stays in the default profile.
- `proof_carried_round_local` costs +5,382 bytes at lr12/q40/minimal_subtree
  (24,790 → 30,172) in exchange for a zero-inversion verifier. This is far
  above the +312–1,008 bytes the design quotes from the old slice — the old
  figure described a different packaging granularity and must not be reused.
  In/out of the frozen profile is decided by the CU delta from
  `stage0-onchain`, in writing, not before.
- Proof bytes at the capacity profile (24.8 KB) sit at the top of the
  design's ~20–24 KB estimate; the Johnson-shaped profile is ~40 KB. Staged
  upload handles both; reported honestly either way.

Corruption suite (host): every variant rejects all of
`root_corruption`, `payload_corruption`, `final_value_corruption`,
`grinding_corruption` (the four required classes) plus
`statement_digest_mismatch`, `trailing_byte`, `truncation`,
`mode_flag_replay`, `profile_swap` — see `crates/aspis-prover/tests/stage0.rs`
and the per-variant records in the JSON artifact.

Solana program hygiene note: the staged upload account now stores a magic
header, proof length, and upload authority. First initialization requires the
proof-account signer and upload-authority signer; chunk upload requires the
stored authority signer; verify remains read-only and statement/proof-only.
This is a Stage 0 seam hardening, not a claim that the later pool is audited.

## 4.1 Measured results (SBF gate matrix, local validator)

Source: `results/stage0/onchain_summary.json`, generated 2026-07-04 by
`cargo run --release -p aspis-xtask -- stage0-onchain-gate`.
Runtime: `solana-test-validator 2.3.0 (src:a2e21dda; feat:3640012085,
client:Agave)`. Verify transaction CU limit: 1,400,000. Heap frame:
262,144 bytes. All soundness labels remain **heuristic**.

| profile | payload | merkle | status | proof bytes | upload chunks | upload CU | verify CU |
| --- | --- | --- | --- | ---: | ---: | ---: | ---: |
| capacity_lr12_q40_g16 | raw_fibers | minimal_subtree | accepted | 24,694 | 39 | 22,036 | 1,063,093 |
| capacity_lr12_q40_g16 | carried | minimal_subtree | accepted | 30,230 | 48 | 25,780 | 1,078,628 |
| johnson_lr12_q80_g16 | raw_fibers | minimal_subtree | **CU exceeded** | 39,478 | 62 | 30,502 | 1,400,000 |
| johnson_lr12_q80_g16 | carried | minimal_subtree | **CU exceeded** | 49,366 | 78 | 37,776 | 1,400,000 |
| capacity_lr14_q40_g16 | raw_fibers | minimal_subtree | **CU exceeded** | 37,308 | 59 | 32,076 | 1,400,000 |

Accepted variants had five identical verify simulations and rejected every
on-chain corruption case. Failed variants report the simulation logs in the
JSON artifact; the common failure is `exceeded CUs meter at BPF instruction`
after the program consumed 1,399,644 of the effective 1,399,700 CU available
after compute-budget instructions.

Stage 0 decision from these numbers:

- `proof_carried_round_local` is **out** for the current frozen profile: it
  costs +5,536 proof bytes and +15,535 CU at lr12/minimal-subtree.
- `minimal_subtree` remains required; independent paths are measured on host
  only and are too upload-heavy to matter for the current gate.
- The capacity lr12 profile fits under the 1.19M Yano ceiling with about 10.7%
  slack. The lr14 diagnostic does not fit the 1.4M transaction cap, but lr14
  is no longer treated as the statement target until §13.8 witness layout is
  frozen by measurement.

## 4.2 Native profiling, g32, and layout-target diagnostics

Source artifacts:

- `results/stage0/onchain_profile.json`
- `results/stage0/onchain_g32_summary.json`
- `results/stage0/layout_sweep.json`

Native lr12/q40/g16 raw/minimal profiling, measured with program CU markers:

| Bucket | CU |
| --- | ---: |
| header + transcript + query derivation | 11,585 |
| layer Merkle verification total | 267,744 |
| layer fold-consistency total | 733,692 |
| final check | 53,611 |
| marker-to-marker total | 1,071,252 |

The marker-to-marker total is higher than the plain verifier simulation
because each marker logs compute units. Use `onchain_summary.json` for the
headline CU number and `onchain_profile.json` for attribution.

Proxy/native breakdown diff:

| Bucket | Phase 2 freeze proxy | Phase 2 full-reuse proxy | Native profiled |
| --- | ---: | ---: | ---: |
| parse/header | 1,482 | 1,486 | 276 |
| transcript/setup | 19,432 | 19,425 | 11,309 |
| OOD | 12,145 | 12,144 | 0 |
| per-round query body | 822,129 | 770,128 | 1,001,436 |
| folding bucket | 12,808 | 12,462 | included in query body |
| final round/check | 49,064 | 49,043 | 53,611 |
| verify/headline | 914,591 | 862,238 | 1,063,093 |
| total including upload | 927,227 | 874,724 | 1,085,129 |

The immediate discrepancy is the per-round body: native is roughly +231K CU
over the closest full-reuse proxy despite similar query count. Setup and
final are not the problem. Suspects carried forward: arity/fold schedule
mismatch, native proof/account streaming overhead inside the round loop, and
the exact split between old proxy "per-round queries" and native local fold
checks.

g32 query/grinding diagnostic:

| profile | status | proof bytes | upload chunks | upload CU | verify CU |
| --- | --- | ---: | ---: | ---: | ---: |
| capacity_lr12_q36_g32 | accepted | 23,510 | 37 | 18,276 | 1,025,729 |
| capacity_lr12_q32_g32 | accepted | 21,078 | 33 | 16,738 | 894,891 |

Both g32 variants rejected all nine on-chain corruption cases. These profiles
are not frozen; they only prove that prover-side grinding can buy meaningful
SBF headroom if Stage 1 soundness accounting permits the lower query counts.

Lower-row layout-target PCS verifier costs:

| profile | status | proof bytes | upload chunks | upload CU | verify CU |
| --- | --- | ---: | ---: | ---: | ---: |
| capacity_lr10_q40_g16 | accepted | 14,768 | 24 | 15,969 | 773,668 |
| capacity_lr10_q36_g16 | accepted | 14,512 | 23 | 13,662 | 742,795 |
| capacity_lr10_q32_g16 | accepted | 12,560 | 20 | 14,431 | 656,662 |

All three lower-row variants rejected all nine on-chain corruption cases.
They use g16 to avoid prover-side grinding variance; verifier-side g32
overhead is one grinding hash and was measured separately in the lr12 g32
artifact.

Corrected synthetic layout sweep, 32 queries, per-query wide leaf hashing plus
naive gamma-RLC recombination:

| log_rows | columns | leaf bytes | leaf hash CU | Merkle CU | RLC CU | total-to-RLC CU |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 12 | 16 | 64 | 5,915 | 71,955 | 49,279 | 127,149 |
| 11 | 32 | 128 | 6,939 | 66,003 | 96,895 | 169,837 |
| 10 | 64 | 256 | 8,987 | 60,051 | 192,127 | 261,165 |
| 9 | 128 | 512 | 13,083 | 54,099 | 382,591 | 449,773 |
| 8 | 256 | 1,024 | 21,275 | 48,147 | 763,519 | 832,941 |
| 6 | 400 | 1,600 | 30,491 | 36,243 | 1,192,063 | 1,258,797 |

Interpretation: a statement layout that lowers rows by exploding to hundreds
of columns is not viable with naive per-query RLC. The next measured target is
lr10/k64/q32, integrated with the real statement evaluator and an optimized
RLC loop. Projection against the 1,190,000 CU verify target:

| target | measured PCS CU | leaf+RLC CU | sumcheck estimate | projected CU | headroom |
| --- | ---: | ---: | ---: | ---: | ---: |
| lr10/k64/q40 | 773,668 | 201,114 | 30,000 | 1,004,782 | 185,218 |
| lr10/k64/q36 | 742,795 | 201,114 | 30,000 | 973,909 | 216,091 |
| lr10/k64/q32 | 656,662 | 201,114 | 30,000 | 887,776 | 302,224 |

The Stage 0 conclusion is recorded separately in
`docs/stage0-conclusion.md`: q32/g32 at lr10/k64 is the only target with
enough measured headroom to justify Stage 1. q36 is reserve. q40 is too tight
for the current single-transaction statement plan.

## 5. Gate checklist (design §7)

| Gate item | Status |
| --- | --- |
| Native slice runs the ported kernels | **PASS** (by construction; see §1) |
| Host verify parity 10/10 | **PASS** (`cargo test` `parity_10_of_10_all_variants` + host_summary) |
| Host/on-chain accept-reject parity | **PASS for continuation target** — lr10 q40/q36/q32, lr12 capacity, and g32 diagnostics accept on-chain and reject corruption; Johnson q80 and lr14 fail due CU as recorded RED diagnostics |
| Measured CU at both profiles, raw artifacts | **PASS/RED** — artifacts committed; Johnson q80 and lr14 exceed CU |
| Corruption tests pass | **PASS for accepting SBF variants** (4/4 classes + 5 extra vectors); failed variants have no accepting baseline |
| Reconciliation note | **PASS** (§2) |
| whir-p3 Johnson divergence recorded | **PASS** (`docs/whir-p3-divergence.md`) |
| Witness layout target frozen | **PASS/CONDITIONAL** — `docs/stage0-conclusion.md` freezes lr10/k64/q32 as the Stage 1 target hypothesis |

**Stage 0 is therefore conditionally closed.** It is a GO into Stage 1 only
for the lr10/k64/q32/g32 capacity-labelled target hypothesis recorded in
`docs/stage0-conclusion.md`. It is a RED for the old lr14 narrow-layout target,
for Johnson q80, and for proof-carried round-local. Stage 1 must kill or
justify q32/g32 in the written soundness note; if Stage 1 requires a schedule
whose measured projection leaves less than roughly 150K CU before constraint
composition, the single-transaction plan RED-stops and split verification
becomes the named fallback.
