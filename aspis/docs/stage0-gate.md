# Stage 0 gate note — substrate consolidation

Date: 2026-07-04. Base repo revision at Stage 0 start: `d0d7605`.
Design reference: "Aspis: Transparent Shielded Spend on Solana — Staged
Design" (2026-07-04), section 7.

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

**Deviation 2 — on-chain measurement environment-blocked.** The authoring
environment's network policy denies both `release.anza.xyz` and GitHub
release downloads (HTTP 403 at the gateway), so `cargo-build-sbf` /
`solana-test-validator` could not be installed and no CU number for this code
exists yet. The complete on-chain runner ships as
`cargo run -p aspis-xtask -- stage0-onchain` (build → local validator →
staged upload → verify CU for every variant → on-chain corruption suite →
`results/stage0/onchain_summary.json`). Gate items that require it are marked
OPEN below.

## 2. Reconciliation note (work item 3)

The design asks for a one-page note reconciling "the proxy freeze, the later
Phase 2 measurements, and the new native numbers".

- **Proxy freeze (927,227 CU) / measured best (852,745 CU)**: not present in
  this tree; not reproducible; treated as design-document context only. There
  is no freeze here to retire, and none of these numbers may be quoted as a
  property of this codebase.
- **Phase 2 measurements that ARE in this tree** (`results/phase2*`,
  regenerable via `cargo xtask phase2-experiments` at the repo root): kernel
  winners `reference_canonical` + `karatsuba` + `late_lift_qm31`; best
  skeleton variant measured at 667,770 CU total; higher-fidelity
  `whir_t100_capacity_full` evaluator at 458,043 CU; real-Winterfell trace-8
  at 1,157,699 CU with recursive variants hitting the 1.4M cap. These
  motivate the substrate choice and the kernel set, and nothing else.
- **New native numbers**: host-side only so far (§4;
  `results/stage0/host_summary.json`). The first CU figures for native v0
  will come from `stage0-onchain`, and the first freeze of this lineage
  (`whir-m31-capacity-v1`) is cut then, not now. Freezing before a CU
  measurement would recreate exactly the internal inconsistency this work
  item exists to remove.

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
the capacity/Johnson profile names denote query-count shapes only.

| profile | payload | merkle | proof bytes (mean) | accept |
| --- | --- | --- | ---: | --- |
| capacity_lr12_q40_g16 | raw_fibers | minimal_subtree | 24,790 | 10/10 |
| capacity_lr12_q40_g16 | raw_fibers | single_paths | 54,060 | 10/10 |
| capacity_lr12_q40_g16 | carried | minimal_subtree | 30,172 | 10/10 |
| johnson_lr12_q80_g16 | raw_fibers | minimal_subtree | 39,616 | 10/10 |
| johnson_lr12_q80_g16 | raw_fibers | single_paths | 99,839 | 10/10 |
| capacity_lr14_q40_g16 | raw_fibers | minimal_subtree | 37,666 | 10/10 |

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

## 5. Gate checklist (design §7)

| Gate item | Status |
| --- | --- |
| Native slice runs the ported kernels | **PASS** (by construction; see §1) |
| Host verify parity 10/10 | **PASS** (`cargo test` `parity_10_of_10_all_variants` + host_summary) |
| Host/on-chain accept-reject parity | **OPEN** — same no_std code path is compiled into the SBF program, but the gate requires execution, not structure; run `stage0-onchain` |
| Measured CU at both profiles, raw artifacts | **OPEN** — blocked in this environment (Deviation 2) |
| Corruption tests pass | **PASS on host** (4/4 classes + 5 extra vectors); on-chain rerun bundled into `stage0-onchain` |
| Reconciliation note | **PASS** (§2) |
| whir-p3 Johnson divergence recorded | **PASS** (`docs/whir-p3-divergence.md`) |

**Stage 0 is therefore NOT closed.** Remaining to close: run
`cargo run --release -p aspis-xtask -- stage0-onchain` on a machine with the
Agave toolchain, commit `results/stage0/onchain_summary.json`, append the CU
table to §4, decide `proof_carried_round_local` in writing, and cut the
`whir-m31-capacity-v1` freeze. Stage 1 (soundness hardening) must not start
before that, per working rule "no stage begins before the previous gate
document is written" — this note becomes the gate document the moment the
OPEN rows flip.
