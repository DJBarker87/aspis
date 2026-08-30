# Aspis V7: transparent private payments on Solana

[![Spend integration](https://github.com/DJBarker87/aspis/actions/workflows/spend-integration.yml/badge.svg)](https://github.com/DJBarker87/aspis/actions/workflows/spend-integration.yml)

Aspis is a transparent, trusted-setup-free zero-knowledge payment system for
Solana. Its on-chain verifier uses Circle STARK techniques. The accompanying
proof work is written in Lean 4 and connected to selected production Rust with
Charon and Aeneas.

One point deserves emphasis. The V7 mathematics no longer relies on a theorem
from the literature being supplied as a premise. The decoding, list-size,
agreement, and classical random-oracle Fiat-Shamir results cited by
earlier versions have been reconstructed in Lean for the exact fields, domains,
and thresholds used by Aspis.

The current V7 design can verify a private transfer or withdrawal, update an
eight-lane pool, record the nullifier, and settle the result in one Solana
transaction. Exact local runtime tests put every measured V7 path below 1.3
million compute units. The earlier V5 verifier has already completed a
finalized mainnet transaction, using 1,334,452 compute units for the full
private-spend verification and state change.

This repository is the `DJBarker87/aspis` cryptography project. It has no
connection with the DeFi product at `aspis.finance`.

## Current results

| Work | Present result | Evidence |
| --- | --- | --- |
| V7 Solana verifier | Complete eight-lane transfer and withdrawal paths execute in one versioned Solana transaction in local runtime tests | [V7 activation record](docs/research/v7-one-tx-activation-20260828.md) |
| V7 formal work | Lean checks the main mathematical arguments and exact calculations. The remaining work applies the final probability theorems directly to the current production program | [V7 formal record](docs/research/v7-one-tx-formal-consolidation-20260828.md) |
| V5 mainnet result | A finalized Solana mainnet transaction accepted the archived 75,358-byte proof, advanced the pool, and marked the nullifier as spent | [V5 mainnet bundle](release/aspis-v5-tag67-mainnet-v1/) |
| V5 end-to-end evidence | Lean mathematics, selected Rust-to-Lean proofs, byte-for-byte reproducible program code, and finalized transaction records are preserved together | [Formal verification](docs/formal-verification.md) |

## What Aspis does

A private spend has a public statement and a secret witness. The statement
names such things as the pool root, output commitment, asset, value, fee, and
nullifier. The nullifier is a public one-use marker that prevents the same note
from being spent twice. The witness contains the owner secret, note opening,
and Merkle path.
The proof shows that the hidden note belongs to the spender and that the state
transition is valid, without publishing the witness.

The Solana program checks the proof before changing state. On acceptance it
advances the selected pool lane and creates the spent-nullifier marker in the
same transaction. A withdrawal also transfers the authorised tokens from the
vault. If any check or write fails, the whole transaction rolls back.

Aspis uses a transparent STARK construction, so there is no trusted setup and
no ceremony-generated proving key. The remaining cryptographic boundaries
include the real-world security of SHA-256 and Poseidon2. Their algorithms and
use in the protocol are modelled in Lean; their resistance to attack remains a
cryptographic assumption.

## V7: one transaction, eight pool lanes

V7 is the current design. It divides the pool state into eight lanes, so
independent spends need not all wait on one shared state update. A successful
transaction does the following:

```text
check the pool and verifier configuration
  -> run the zero-knowledge verifier
  -> receive a fixed-size result
  -> update the pool lane and spent-nullifier record
  -> transfer SPL tokens as well, if this is a withdrawal
```

The following figures are complete transaction measurements. They include the
pool program, the proof verifier, account checks, state changes, and the token
transfer for a withdrawal. Each figure comes from one measured execution.

| V7 operation | History storage | Compute units | Transaction bytes | Margin below 1.3M CU |
| --- | --- | ---: | ---: | ---: |
| Private transfer | Current page | 1,145,890 | 799 | 154,110 |
| Private transfer | New page | 1,191,463 | 832 | 108,537 |
| Withdrawal | Current page | 1,136,135 | 964 | 163,865 |
| Withdrawal | New page | 1,201,757 | 997 | 98,243 |

An invalid proof that has not completed the required proof-of-work is rejected
after 61,309 CU and leaves every account byte unchanged. The evidence files
record the program and proof hashes, transaction sizes, execution logs, and
account changes.

These measurements use LiteSVM with the same 1,400,000-CU limit used by the
target runtime. V7 has not been submitted to devnet or mainnet. Before that
happens, the remaining formal proofs must be joined to the current production
source, the final program binaries must be reproduced independently, and the
whole account lifecycle must be tested on a public network.

The [V7 activation record](docs/research/v7-one-tx-activation-20260828.md)
contains the binaries, hashes, commands, and full test record. The [compute
report](docs/research/v7-cu-sparsity-lock-20260828.md) gives the lower-level
performance details.

## Formal verification

The formal work has two connected parts:

1. [`AspisFormal/`](AspisFormal/) contains the Lean models and proofs for the
   spend rules, Merkle authentication, proof checks, challenge sampling, and
   concrete security calculations.
2. [`aeneas-verif/`](aeneas-verif/) uses Charon and Aeneas to translate
   selected Rust functions into Lean, where their behaviour can be compared
   with the mathematical models.

### The cited mathematics is now proved here

Early Aspis work used published results for three substantial steps. V7 now
contains its own Lean proofs of all three:

1. the exact list-decoding bounds, including the concrete maximum list sizes;
2. the agreement argument used to carry possible answers through the folding
   stages of the proof; and
3. the classical random-oracle argument that connects the interactive proof
   to its Fiat-Shamir form.

Each proof is specialized to the actual Aspis parameters. The theorem
statements contain no generic premise that merely repeats the desired
conclusion. The main theorem files print their axiom dependencies, whose
complete union is the ordinary Lean foundation used by this project:

```text
propext
Classical.choice
Quot.sound
```

There is no project-specific axiom or paper theorem hidden behind those
declarations. The [decoding and agreement
record](docs/research/v7-exact-correlated-agreement-audit-20260827.md) and the
[Fiat-Shamir compiler record](docs/research/v7-k1.6-fs-aok-compiler.md) give
the theorem-by-theorem evidence.

For V7, Lean already checks the two Merkle trees, the finite query and
challenge calculations, the main polynomial relations, the random-oracle
execution model, and the final error accounting. It also handles the case in
which an attacker asks the random oracle a question before the verifier asks
the same question and later receives the cached answer.

Two kinds of proof work remain. Some probability theorems still have to be
applied to the exact events produced by the current program. A few Rust parsing
and control-flow paths also need to be translated from the current source.
These are tracked as named proof obligations. The numerical security
accounting has not been relaxed to make the proofs fit.

Lean checks the model stated in each theorem. Compiler correctness, Solana
runtime behaviour, and the security of SHA-256 and Poseidon2 retain their own
clearly stated assumptions. The [V7 formal
record](docs/research/v7-one-tx-formal-consolidation-20260828.md) gives the
theorem names and exact remaining obligations for specialist review.

## V5 mainnet transaction and end-to-end evidence

V5 is the finalized on-chain baseline. On 25 July 2026 in Europe/Berlin, or 24
July UTC, the deployed Aspis program verified the complete archived proof on
Solana mainnet-beta. It then advanced the pool and recorded the nullifier as
spent.

[View the finalized transaction on Solana Explorer](https://explorer.solana.com/tx/EJviPgF12i9iK2CveVaQSMeFQqDMFPQ1iPRUYEwNQE3zGquTUZNJXPZEENorcQtsnQj1orFmH1TPsgdbR3vJ2fE?cluster=mainnet-beta)

| Item | Finalized V5 record |
| --- | --- |
| Transaction | `EJviPgF12i9iK2CveVaQSMeFQqDMFPQ1iPRUYEwNQE3zGquTUZNJXPZEENorcQtsnQj1orFmH1TPsgdbR3vJ2fE` |
| Slot | `435019536` |
| Program | `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue` |
| Proof | 75,358 bytes |
| Compute used | 1,334,452 CU |
| Transaction limit | 1,356,912 CU |
| Nullifier | `7Umhkv2Z3E2DksnpivCz2tovtbRoL1uXtnYBAtQBgu8Q` |
| Compiled Solana program | 1,258,496 bytes |
| Program SHA-256 | `4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40` |

The V5 evidence chain preserves four separate links:

1. Lean checks the private-spend rules and the main mathematical calculations
   used by the proof system.
2. Charon and Aeneas translate selected verifier Rust into Lean. Lean then
   follows one complete successful verifier run, from parsing through the
   final checks.
3. Pinned source and build tools reproduce the exact deployed program bytes.
4. The mainnet archive reconstructs the proof from 79 finalized uploads and
   the program from 1,466 finalized loader writes, then checks the transaction,
   state change, cleanup, and refund records.

The clean replay of this complete successful path passed on 24 August 2026.
Its final results are derived from the same translated execution rather than
being supplied by the caller. The [formal verification
record](docs/formal-verification.md) explains the remaining field-by-field link
between the public statement in Rust and its mathematical model.

The archived proof also passes the released verifier callback in regression
tests. Changing any one of the nine public fields causes rejection. The proof
account and ProgramData were closed after the demonstration, so the
[payer RPC archive](release/aspis-v5-tag67-mainnet-rpc-archive-v1/) is the
permanent reconstruction record.

## Reproduce the evidence

### Lean development

```bash
cd AspisFormal
lake exe cache get
lake build
```

Many research notes give smaller focused targets for reviewers who do not
wish to rebuild every Lean file. Start with [formal
verification](docs/formal-verification.md) and the [V7 formal consolidation
note](docs/research/v7-one-tx-formal-consolidation-20260828.md).

### Rust-to-Lean replay

The maintained Lean 4.32 replay lives under
`aeneas-verif/v5-result-aware-source-link-20260821/`. The [Aeneas replay
notes](aeneas-verif/README.md#replaying-the-final-accepted-path-theorem) record
the pinned tools, generated inputs, and dependency caches.

### Exact V5 program and release inputs

```bash
./release/aspis-v5-tag67-frozen-candidate-v1/verify.sh
```

The [V5 release preflight](release/preflight/v5-production-freeze.md) pins the
source, Agave release, platform tools, and provenance used for a byte-for-byte
rebuild.

### Finalized V5 mainnet lifecycle

```bash
./release/aspis-v5-tag67-mainnet-v1/verify.sh
python3 tools/check_release_facts.py
```

These offline checks verify the published proof and statement, compiled
program, lifecycle receipts, compute values, cleanup accounting, and committed
hashes.

## Scope and limitations

V7 is an active release candidate. Its local execution evidence is complete
for the measured paths, while the remaining source and probability links are
still being proved. No V7 transaction has been signed or submitted.

V5 demonstrates one private input, one private output, and one sequential pool.
The demonstration anonymity set was one. It does not include a wallet,
deposits, multiple inputs or outputs, or a growing privacy set. Its 75,358-byte
proof required a temporary account and 79 upload transactions before sealing.

The remaining assumptions concern the cryptographic strength of Poseidon2 and
SHA-256, faithful translation and compilation, and Solana runtime behaviour.
Network metadata, timing, fee-payer linkage, transaction graphs, and physical
side channels lie outside the proved privacy view. The project has extensive
formal proofs, tests, reproducible builds, and finalized chain evidence; it has
not yet received an independent cryptographic or Solana security audit.

The demonstration witness was freshly generated for the release. It did not
represent a user's funded private note, and the secret witness was neither
published nor retained.

## Repository guide

| Path | Contents |
| --- | --- |
| `AspisFormal/` | Lean 4 mathematical, probability, and program-execution proofs |
| `aeneas-verif/` | Charon/Aeneas generated Lean and source-to-model bridges |
| `crates/aspis-core/` | Fields, transcript, proof format, commitments, and verifier arithmetic |
| `crates/aspis-statement/` | Private-spend statement and relation |
| `crates/aspis-prover/` | Prover, grinding, fixtures, and security calculators |
| `programs/aspis-verifier/` | Solana STARK verifier program |
| `programs/aspis-pool/` | V7 pool, lane, history, nullifier, and withdrawal logic |
| `xtask/` | Build, deployment, recovery, and evidence tools |
| `release/` | Frozen release inputs and finalized public bundles |
| `results/` | Runtime measurements, binary hashes, and replay records |
| `docs/` | Design explanations, source maps, assumptions, and research audits |
| `paper/aspis-formalization/` | Formalization report |
| `paper/aspis-spend/` | Construction and deployment paper |

For a short introduction, see [How Aspis works](docs/how-it-works.md). The
[assumptions ledger](docs/assumptions-ledger.md), [security
policy](SECURITY.md), and [V5 accepted source
map](docs/v5-accepted-source-map.md) provide the review boundaries.

## Earlier result

An earlier feasibility release remains preserved. Its finalized
[mainnet transaction](https://explorer.solana.com/tx/3G1voggszvDMGi5PbGM1kuEMYKvh2TNMbH6hHHwndUdRQJNT7ehRFpQpksxLnx5tp2xkS5jGi359rVXk42sRPFcv?cluster=mainnet-beta)
used 1,344,003 CU on 16 July 2026. The [historical mainnet
record](docs/mainnet-demo.md) contains its proof and immutable evidence.

## Project

Dominic Barker built Aspis as a solo research project with AI-assisted
engineering. Citation metadata is in [CITATION.cff](CITATION.cff).

Licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE).
