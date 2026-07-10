# Aspis: Transparent Shielded Spend on Solana - Staged Design

Working title: `Aspis` (rename freely; used here only as a namespace).
Date: `2026-07-04`
Status: design frozen for Stage 0 start; Stage 0 measurement addendum recorded
on `2026-07-04`.

## 1. Objective

Build and measure the first transparent, trusted-setup-free,
plausibly-post-quantum verifier of a real private-payment statement running as
a program on Solana, and package it so that a production team can adopt the
verifier layer without touching the demo application.

One sentence per property:

- **Transparent**: no trusted setup anywhere in the stack; all parameters are
  public randomness.
- **PQ-leaning**: security rests on hash functions and information-theoretic
  arguments only; no pairings, no elliptic curves, no lattice assumptions in
  the proof system.
- **Real statement**: a single shielded-spend atom (membership + ownership +
  non-double-spend + range), not a toy AIR.
- **On Solana**: verified by an SBF program under the current `1,400,000` CU
  per-transaction cap and `1232`-byte transaction size, with staged upload
  where needed.
- **Adoptable**: the verifier ships as a standalone permissively licensed crate
  with a headline CU number; the shielded pool is a separate demo program that
  consumes it.

## 2. Positioning

- `ePrint 2025/1741` (the vendored Yano baseline) demonstrated a transparent
  PQ STARK verifier on Solana, but for a minimal affine AIR bound to
  `SHA256(cipher)`: a verifier without a statement.
- StarkWare's `STRK20` (June 2026) demonstrated the exact statement class:
  note-based shielded pool, spend proofs checking membership, ownership, and
  non-double-spend on a transparent PQ stack, but on Starknet, a chain with
  native in-protocol proof verification.
- Every shipped Solana privacy system named in the source design (Light v1,
  Elusiv, nullifier.cash, Darklake) is Groth16 over bn254: trusted setup, not
  PQ.

Aspis is the union: STRK20's statement class, verified Yano-style inside
Solana's constraints. Nobody has published this as of the novelty check run on
`2026-07-04`; rerun the check in Stage 5 before any public claim.

## 3. Claim Boundary

### Strongest defensible positive claim

For one pinned code revision, one pinned proof configuration, and one pinned
Solana runtime setup, this repo implements a hiding, transparent, hash-based
proof of a shielded-spend statement (Merkle membership under a public anchor,
nullifier derivation, value range, public binding), generates and locally
verifies those proofs, and accepts them on Solana devnet within the documented
`1.4M` CU per-transaction cap, with raw `n = 100` devnet measurements
published.

### Strongest defensible negative claim

After implementing and adversarially testing the statement layer on the
hardened multilinear PCS, the resulting proof bytes, upload pressure, or
on-chain verifier cost exceed the stated Solana constraints; a transparent
shielded-spend atom is therefore not feasible within this pinned stack.

### Explicitly out of scope

- Production readiness, audits, mainnet deployment
- Relayer infrastructure, fee privacy, wallet UX
- Multi-asset pools, swaps, private DeFi composition
- Compliance / viewing-key machinery
- Recursion, aggregation, batching of spends
- Any claim of equivalence to paper WHIR
- Any "first" claim without the Stage 5 novelty re-check

## 4. Architecture

Three layers, one hard rule:

```text
Layer 3: demo pool program        (aspis-pool)       shield / spend / nullifier set
Layer 2: statement layer          (aspis-statement)  spend atom -> multilinear constraints -> sumcheck
Layer 1: proof substrate          (aspis-verifier)   hardened native WHIR-style M31 PCS, host + SBF
```

### The Two-Hash Rule

- **Inside the circuit** (note commitments, Merkle tree, nullifier PRF): use an
  algebraic hash over M31, Poseidon2-M31 unless Stage 2 finds a better-analyzed
  alternative. Arithmetizing SHA-2/3 in-circuit is banned here.
- **On-chain and in the proof's own Merkle/transcript structure**: use SHA-256
  via the Solana syscall, exactly as native v0 does today. The on-chain
  verifier never recomputes a note-tree path; that computation lives inside
  the proven statement.

### Substrate Choice

Native WHIR-M31 v0 is the substrate, not Winterfell. Phase 2 real-Winterfell
measurements showed trace-8 already at `1,157,699` CU with recursive variants
hitting the cap. Native v0 verified on-chain at `326,021` CU with `1,073,979`
CU of headroom in the design context. The price is that this repo owns the
soundness argument, so Stage 1 is load-bearing.

### Statement Proof-System Shape

The substrate is a multilinear opening scheme, so the statement layer is a
multilinear constraint system (Spartan/HyperPlonk-shaped), not a univariate
AIR.

1. The witness is laid out as a wide table with `k` columns over the
   hypercube, committed in one Merkle tree with row-packed leaves. One tree
   shares query paths across columns; `k` separate commitments are rejected.
2. Constraints are row-local. No shifted/rotated operands; Poseidon2 rounds
   are unrolled across columns to satisfy this.
3. Pointwise satisfaction is proved by a zerocheck:
   `sum_x eq(r, x) * C(w_1(x), ..., w_k(x)) = 0`. A plain sum of `C` is too
   weak because cheating rows can cancel.
4. Sumcheck terminates at random point `z` with claimed column evaluations
   `v_1, ..., v_k`; the verifier checks `eq(r, z) * C(v_1, ..., v_k)` against
   the final sumcheck message.
5. Claimed evaluations are checked by RLC batching: sample `gamma`
   post-commitment, define `w* = sum gamma^i * w_i`, and run the PCS opening
   on `w*` at `z` with claimed value `sum gamma^i * v_i`. At each PCS query,
   the verifier recombines the opened row into the `w*` value before folding.

Consequences: the proof envelope changes (wide leaves, claimed per-column
values, `gamma` in the transcript), and the PCS must accept an externally
supplied evaluation claim `(z, v)` as an absorbed public input. This is a
substrate interface change audited in Stage 1 and implemented in Stage 2.

## 5. Naming and Honesty Rules

- Do not call the substrate "WHIR" in any public claim. It is a
  **WHIR-style multilinear PCS**. The whir-p3 cross-validation showed the
  local schedule is not upstream-equivalent, and v0 deviates from the paper.
- Every published number carries its soundness label: `proven`,
  `conjectured`, or `heuristic`, with the assumption named.
- The capacity-vs-Johnson asymmetry from Phase 2 must be stated wherever a CU
  number is quoted.
- The claim boundary in section 3 ships in the README, not just the paper.

## 6. CU and Byte Budget

Solana constants: `1,400,000` CU per transaction; `1232`-byte transactions;
staged upload assumed (`640`-`900` byte chunks).

| Component | Basis | Value | Status |
| --- | --- | ---: | --- |
| PCS verify, native v0 target profile (`log_rows=12`) | measured on-chain | `326,021` CU | measured, pre-hardening |
| PCS verify after Stage 0 kernel port | minimal_subtree + batch inversion deltas from Phase 2 | material reduction expected | projection only |
| PCS verify at `log_rows=14` | extra fold round and query-path levels | `+25-35%` over `log_rows=12` | estimate |
| Soundness-hardening overhead | Stage 1 audit | unknown | unknown |
| Sumcheck verification, ~14 rounds, degree <= 6 | field-op counting | `< 30,000` CU | estimate |
| Constraint composition at opened point | SBF measurement | unknown | Stage 2 gate |
| Upload CU for ~20 KB proof | native v0 measured `38,965` CU at `18,316` bytes | `~40-50K` CU | estimate |
| Proof bytes | v0 target + sumcheck + masking | `~20-24` KB | estimate |
| Verify transaction target | budget ceiling | `<= 1,190,000` CU | target |

Stage 0 measurement correction (`2026-07-04`): the `326,021` CU row was a
q=8 profile and must not be used as the honest security-budget anchor. The
first native q40/g16 capacity measurement is `1,063,093` CU at lr12
raw/minimal, with `proof_carried_round_local` worse on both bytes and CU. The
lr14 row above is demoted to a narrow-table diagnostic: it exceeded the
transaction cap, but §13.8 witness layout is the real decision that sets the
target row count. The measured Stage 0 continuation target is
lr10/k64/q32/g32, projected at `887,776` CU before Stage 1 hardening and
Stage 2 constraint-composition costs. q32/g32 is a Stage 1 soundness
hypothesis, not a public claim. Stage 0 is therefore a conditional GO to Stage
1 for that target, RED for lr14 and Johnson q80.

Stage 1 amendment (`2026-07-10`, frozen): the soundness note retired q32/g32
and ruled q36/g32. Upstream T1/T2 constants are pinned; the v3 envelope
enforces external and per-round OOD evaluations through an interleaved
degree-6 relation sumcheck and implements the canonical two-phase PCS
boundary `C1 -> (lambda,chi) -> C2 -> claims -> gamma`. The literal
lr10/q36/g32 verifier is `943,972` CU and the current combined projection is
`1,175,086` CU, leaving only `14,914` CU against the 1.19M target before
unpriced constraint composition. Stage 1 is closed as a PCS milestone, but
the 10% product-feasibility slack gate is red. These figures supersede the
Stage 0 continuation projection; they do not retroactively alter the Stage 0
gate.

Do not trust the Phase 1 additive model's per-op coefficients for the
statement layer. Constraint-evaluation cost is measured directly on SBF or not
believed at all.

Separate deposit-path cost: inserting a note commitment requires roughly `32`
software Poseidon2-M31 permutations on-chain. Cost per permutation on SBF is
unmeasured. Stage 2 measures it and either fits the cap or records a named
scope change (batched insertion or indexer-computed root accepted under
proof).

## 7. Stage 0 - Substrate Consolidation

The repo currently disagrees with itself, and the native slice uses none of
the measured wins. Fix that before touching cryptography.

Work items:

1. Port the winning Phase 2 configuration into native v0: `minimal_subtree`
   Merkle mode, `raw_fibers` fold payload, `round_batch_inversion`, and
   evaluate `proof_carried_round_local` against its proof-byte cost.
2. Re-measure both profiles on-chain; rerun all four corruption tests.
3. Re-freeze as `whir-m31-capacity-v1` or retire the proxy freeze explicitly.
4. Record the whir-p3 Johnson divergence (local starting folding PoW `13`
   bits versus upstream `36`) as an open Stage 1 soundness question.
5. Pull §13.8 forward before closing Stage 0: sweep `(log_rows, k)` for a
   statement-realistic synthetic table, because the lr14 target was a
   narrow-layout assumption rather than a frozen requirement.

Gate (`GO` requires all):

- native slice runs the ported kernels with host/on-chain accept-reject parity,
  `10/10` verify
- measured CU at both profiles recorded with raw artifacts
- corruption tests pass
- one-page note reconciles the proxy freeze, Phase 2 measurements, and new
  native numbers
- witness layout target frozen in writing or explicitly scoped as still open

## 8. Stage 1 - Soundness Hardening

Native v0's documentation says it proves transcript-bound local fold
consistency and is not yet the full WHIR paper path. A statement layer on an
unsound PCS is worthless, so this stage closes or precisely bounds that delta.

Audit checklist:

- OOD samples binding the committed function across rounds
- sumcheck/fold interleaving tying each round's claimed evaluation to the
  previous round's function
- final-round degree/length check on the terminal object
- proximity-parameter accounting: rate, queries per round, grinding, target
  regime (UD / Johnson / capacity), explicit bits per round
- domain shifting / indexing correctness between rounds
- Fiat-Shamir ordering: everything absorbed before anything derived
- grinding witnesses checked on-chain
- evaluation-claim binding for externally supplied `(z, v)`
- batched-opening soundness for the `gamma` RLC argument and its
  Fiat-Shamir order
- copy-argument soundness (LogUp multiset term per amended §13.8): tuple
  compression and pole-collision terms, challenge ordering (interfaces
  committed before `lambda`, `z`), and the second commitment phase this
  forces on the PCS interface
- per-round proximity recomputation for the implemented fold schedule (the
  native v0 schedule at lr10 is 4 committed arity-4 rounds with domain and
  degree both shrinking 4x per round — the rate does NOT improve across
  rounds as WHIR's domain-halving schedule assumes; the per-round query
  budget table must be computed for the schedule as implemented, not the
  Phase 2 two-round shape)

Deliverables:

1. `docs/aspis-soundness-note.md`: reduction from implemented protocol to a
   stated proximity assumption, with a numeric soundness budget for each
   frozen profile.
2. Missing checks implemented in host + SBF verifier, re-measured.
3. Adversarial vector suite beyond bit flips: wrong-evaluation claims,
   off-domain openings, round-skipping, grinding-forgery attempts,
   mixed-profile replay, and **challenge-order attacks** (gamma sampled
   before the claimed column evaluations are absorbed; chi sampled before
   the interface commitment C1) — the gamma-before-claims ordering was
   caught in soundness-note review as a full statement-layer bypass and the
   ordering must be enforced by failing tests, not prose (soundness-note §2).

Gate: soundness note complete, checks implemented, adversarial suite rejecting
`100%`, hardened verifier CU recorded. Stop if the hardened verifier exceeds
roughly `700K` CU at `log_rows=14`.

## 9. Stage 2 - Statement Layer

### SpendV0-min

Public inputs: `anchor`, `nullifier`, `output_commitment`, `asset_id`, `fee`.
Reuse the existing `SpendV0Binding` digest binding unchanged.

Witness relations over M31 with Poseidon2-M31 as `H`:

1. `note = H(owner_pk, value, asset_id, salt)`.
2. `MerkleVerify(note, path, anchor)`, depth `32` unless the demo explicitly
   chooses depth `20`.
3. `nullifier = H(nk, salt)` and `owner_pk = H(nk)` or equivalent key
   schedule.
4. `0 <= value < 2^30` and `0 <= value_out < 2^30`, with
   `value_out + fee = value`. The `value_out` range check is mandatory to
   prevent field-wrap inflation when `fee > value`.
5. Public binding: all public inputs equal the transcript-absorbed statement
   digest fields.

### Sizing Envelope

Poseidon2-M31 width `16`, S-box `x^5`, digest of `8` M31 limbs unless the
8-vs-9+ limb decision changes. An 8-limb digest is about `124`-bit collision
resistance, marginally below a strict `128`-bit target, so this is a written
decision item.

Expected statement shape: roughly `40` Poseidon2 permutations, witness
plausibly `2^13`-`2^14`, sumcheck degree roughly `<= 6-7` with `eq`.

Discipline:

1. Build the no-proof direct evaluator first. Its first test corpus is the
   economic attack surface, not happy-path proof plumbing: field-wrap
   inflation (`fee > value` and unconstrained `value_out`), wrong asset/public
   binding, wrong anchor/path, forged ownership/nullifier, double-spend
   replay, and boundary values at `0`, `2^30-1`, and `2^30`. Add valid vectors
   and differential tests against an independent Poseidon2-M31
   implementation in the same evaluator milestone.
2. Measure real witness size and constraint counts from the evaluator.
3. Measure constraint-composition evaluation cost on SBF in isolation.
4. Measure software Poseidon2-M31 permutation cost on SBF.
5. Only then wire prover -> proof -> hardened verifier.

Gate: evaluator vector-complete; host proof verifies end to end; projected
on-chain total under `1.19M` CU with at least `10%` slack. Stop if the
projection exceeds the budget after one explicit shrink attempt.

## 10. Stage 3 - Hiding Layer

A transparent opening scheme is succinct but not hiding. Without this stage,
the proof leaks witness information and the word "shielded" is unearned.

Components:

1. Commitment hiding: salt/blind committed leaf values so proof-tree Merkle
   openings reveal masked data only.
2. Sumcheck/evaluation hiding: masking-polynomial approach; commit a
   low-degree random mask `rho`, prove the masked claim, and open the
   combination.

Deliverable: `docs/aspis-hiding-note.md`, stating what is hidden, what leaks
(proof size, timing, public inputs), and the argument for each. Gate: hiding
implemented on host and chain, measured deltas recorded, and leakage-shaped
checks added.

## 11. Stage 4 - Crate Seam and Demo Pool

Crate seam:

- `aspis-core`: field tower, hashing, transcript, sumcheck, PCS logic;
  `no_std` compatible and byte-exact between host and SBF.
- `aspis-verifier`: crate + program for proof envelope parsing and
  verification only. It knows nothing about spends. Public API:
  `verify(profile_id, statement_digest, proof_bytes)`.
- `aspis-prover`: host-only proving.
- `aspis-pool`: demo program with note tree, `shield`, `spend`, nullifier PDA
  creation, and staged upload.

Acceptance test for the seam: prove and verify a different toy statement
through `aspis-verifier` without touching `aspis-pool`.

Packaging:

- Apache-2.0 / MIT dual license.
- README first line: measured verify CU + proof bytes + soundness label.
- Claim boundary in section 3 verbatim in README.
- Every number backed by a reproduction script under `experiments/aspis/...`.
- Devnet IDs and scripted end-to-end demo: shield -> spend -> double-spend
  rejected.

Gate: end-to-end devnet flow succeeds; double-spend and all adversarial
vectors rejected on-chain; seam acceptance test passes.

## 12. Stage 5 - Measurement, Freeze, Writeup

1. Freeze one revision, one profile, one runtime.
2. Run `n = 100` successful devnet spend verifications: mean / median / min /
   max CU, proof bytes, upload transaction count, exact transaction
   signatures.
3. Re-run the novelty scan (Solana transparent verifiers, STRK20 successors,
   Helius/Light output since `2026-07`).
4. Write an ePrint-style measurement study positioned against Yano, STRK20,
   zkDilithium, and Groth16 incumbents. Publish repo and paper together.

Gate: raw artifacts published; every public claim traceable to a script;
claim boundary and soundness labels present in README and paper.

## 13. Decisions Requiring a Written Record Before Code

1. Tree depth `32` vs `20` for the demo pool.
2. Poseidon2-M31 instance: width, round numbers, digest limbs, and source of
   parameter analysis.
3. Soundness regime targeted for the headline claim. **Decided `2026-07-04`:
   headline frozen at `t = 100` bits, capacity-conjectured.** Rationale (the
   field-ceiling lemma, soundness-note §3): `|QM31| = p^4 ~ 2^124`, and every
   algebraic soundness term in the system — proximity-gathering terms per fold
   round, OOD binding, sumcheck Schwartz-Zippel, `gamma`-RLC batching, the
   copy-argument terms — carries a `2^124` denominator that grinding does not
   offset (grinding buys back query-sampling error only). The `2026-07-10`
   upstream pin resolves the algebraic union to `~103.95` bits at the ruled
   `L <= 40` capacity-conjecture clause, and combining it with the 104-bit
   query term yields `~102.98` system bits; `128` bits was never reachable on
   M31/CM31/QM31, consistent with
   upstream evidence (WHIR-JB needing Goldilocks3 for 128-bit settings; the
   M31 circle-STARK ecosystem targeting `~96-100` bits). Changing field towers
   is a different project. The `~124`-bit field ceiling and the `~124`-bit
   8-limb Poseidon2 digest land the whole system on one coherent
   `~100-bit / conjectured / capacity` label with no weakest-link asymmetry.
4. `proof_carried_round_local` in or out of the frozen profile. Stage 0
   measurement says **out** for native v0.
5. Nullifier key schedule; cite a standard shape rather than inventing one.
6. Deposit-path plan if software Poseidon2 insertion is too expensive
   on-chain.
7. Range width (`2^30` fits one M31 limb cleanly).
8. Witness column layout: number of columns `k`, wide-leaf packing format, and
   `gamma` RLC batching parameters. **Amended `2026-07-04`: the lr10/k64
   cost-freeze is not constraint-realizable as originally shaped, and the
   layout freeze becomes "lr10, `k ~ 64-80`, rounds-per-row blocks, boundary
   interface columns, LogUp-style multiset copy check".** Why: the spend
   witness is dominated by sequential Poseidon2 chains (32 Merkle levels where
   permutation i's output is permutation i+1's input), and row-locality forces
   one of three shapes. (a) Fully self-contained rows — one permutation per
   row — needs `k ~ 352` columns, and the measured RLC scaling (`192,127` CU
   at `k = 64`, linear in `k`) prices that at `~1.1M` CU of recombination
   alone: dead. (b) Chaining across rows is exactly the shifted operand this
   design bans, and multilinear shifts are not the univariate `g*z` trick — a
   shifted polynomial's evaluation is not a point-opening of the original.
   (c) The adopted shape: pack a block of rounds per row, commit the chain
   interface state as boundary columns, and prove multiset equality between
   chain-outputs and chain-inputs with a LogUp-style logarithmic-derivative
   argument fused into the statement sumcheck. Consequences the later stages
   must absorb: the copy argument brings its own soundness terms (all with
   `/|QM31|` denominators — folded into the §3 ceiling budget) and requires a
   **second commitment phase** (the LogUp helper column depends on a
   challenge sampled after the interface columns are committed), which is a
   PCS interface change of the same kind as the external `(z, v)` claim.
   Stage 1's soundness note must be written for THIS layout — a note written
   for a layout Stage 2 cannot build is wasted work.

## 14. Risk Register

| Risk | Likelihood | Impact | Mitigation / stop |
| --- | --- | --- | --- |
| Soundness delta larger than expected; hardened verifier blows CU budget | medium | fatal | Stage 1 stop condition; bounded negative fallback |
| Constraint-composition evaluation expensive on SBF | medium | high | isolated SBF measurement before integration |
| Poseidon2-M31 parameter weakness / thin analysis | low-medium | high | cite established parameter sets only |
| Deposit insertion cost over cap | medium | medium | batched insertion fallback, named scope change |
| Proof bytes drift past ~`24` KB | low | low | staged upload; report honestly |
| Scooped during build | low-medium | medium | novelty re-check at Stage 5 |
| Solo-beginner cryptography error surviving publication | medium | reputational | adversarial suite, line-by-line review, external expert pass |

## 15. Source Manifest Additions

- Poseidon2 paper and Plonky3 `p3-poseidon2` M31 instantiation
- Spartan / HyperPlonk
- Zcash protocol spec
- Light Protocol v1 program
- `ePrint 2025/1741`
- STRK20 technical paper
- Upstream `WizardOfMenlo/whir` at the pinned commit

## 16. Working Rules

- No STARK/PCS proof generation for the statement before the direct evaluator
  matches the pinned vector corpus.
- No public number without a reproduction script and a soundness label.
- No stage begins before the previous gate document is written.
- Scope deviations are named as deviations, never silently absorbed.
- Every stage that can fail has a stop condition that produces a publishable
  bounded negative.
