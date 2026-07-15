# Aspis

[![Spend integration](https://github.com/DJBarker87/aspis/actions/workflows/spend-integration.yml/badge.svg)](https://github.com/DJBarker87/aspis/actions/workflows/spend-integration.yml)

Aspis is a shielded payment system whose spend proofs are verified directly
on Solana L1 — no trusted setup, no off-chain verifier. Transparent proofs
are large, and Solana caps every transaction at 1.4 million compute units,
which has kept transparent proof verification on L1 out of reach. Aspis
Spend, the q18/g37 release in this repository, verifies a full
shielded-spend proof, advances the pool state, and records the nullifier in
one transaction under that cap.

This is a research release, not an audit or a production service; the exact
claim, model, and limitations are stated in the
[paper](paper/aspis-spend/) and in [Limitations](#limitations).

Status: certified locally; mainnet execution pending. This page gains the
finalized transaction, compute, and cost evidence when it lands. The
[novelty re-scan](docs/novelty-rescan-2026-07-13.md) is a dated
public-evidence search for the claim shape; no first-execution claim is made
before a finalized mainnet signature exists.

## Release numbers

| Result | Value |
| --- | ---: |
| Proof | 64,447 bytes (fixed layout) |
| Soundness floor (work-normalized, proven Johnson/MCA regime) | 100.16 bits |
| Witness hiding | 103.02 bits pairwise, 104.02 bits versus simulator |
| Verification budget | fits Solana's 1,400,000-CU transaction cap |

The soundness floor is work-normalized: an adversary limited to T
random-oracle queries, 1 ≤ T ≤ 2^128, falsely accepts with probability at
most T · 2^−100.16. The raw acceptance bound at large T is not booked as the
floor; the normalization and both interval endpoints are stated in the
paper.

## No trusted setup

Groth16 proofs are a few hundred bytes and cheap to verify, but their
soundness depends on a multi-party setup ceremony: a participant who
retained the ceremony's secret randomness could forge proofs, and a forged
spend inside a shielded pool is not detectable. Shielded pools live on
Solana verify ceremony-based Groth16 proofs or delegate proof verification
to off-chain systems
([comparison record](docs/novelty-rescan-2026-07-13.md)).

Aspis has no ceremony. Its parameters are public constants, and its security
reductions rest on the hash assumptions stated in the paper — a concrete
Poseidon2 assumption and SHA-256 modeled as a random oracle — rather than on
a reference string with a trapdoor. The cost is proof size: 64,447 bytes
against a few hundred for Groth16. That size gap is the obstacle the
transaction design below addresses.

## One transaction

![Proof upload, sealing, and one-transaction verification with atomic state transition](docs/assets/transaction-flow.svg)

A 64,447-byte proof exceeds Solana's 1,232-byte transaction packet limit, so
it is uploaded once and verified in place:

1. The prover uploads the proof in 68 chunks to a program-owned account.
2. The account is sealed after its complete byte image is checked against
   the released proof digest.
3. One transaction then verifies the sealed proof, advances the pool,
   records the nullifier, and refunds the proof account — atomically. If
   any step fails, no state changes.

A spend therefore costs 70 setup transactions (proof-account create, 68
chunk uploads, finalize) before the verification transaction, plus 2 per
pool (create, initialize). Spends within one pool are strictly sequential:
each proof binds the pool's current sequence number. The proof account's
rent is held until the verification transaction refunds it.

## Construction

The parameters are chosen to fit complete verification under Solana's
compute-unit cap. The commitment layer is WHIR-style rather than FRI because
the cap prices verifier queries, not prover time.

- **Field.** M31 (p = 2³¹ − 1) with its circle group as the evaluation
  domain; Mersenne arithmetic is cheap on the 32-bit SBF target, and the
  degree-four extension QM31 supplies sampling soundness.
- **Hash.** Poseidon2 over M31 (width 16) for note commitments, nullifiers,
  and owner derivation — algebraic, so cheap inside the relation. SHA-256 is
  the Fiat–Shamir oracle because SBF exposes a native SHA-256 syscall.
- **Commitment.** A custom circle-domain, WHIR-style multilinear PCS —
  batched multilinear evaluation with four arity-four folds; it is not an
  invocation of an unmodified WHIR parameter set.
- **Rate.** 1/512 (2¹⁰ message rows to 2¹⁹ circle symbols) — high blowup
  buys per-query soundness, so few queries are needed, which is what the
  compute-unit cap rewards.
- **Queries.** q = 18 per branch, sampled without replacement, with three
  query branches per attempt.
- **Grinding.** 37-bit batch work, per-fold work of 34/33/30/25 bits, and
  32-bit final work — grinding supplies soundness bits that additional
  queries could not fit in the compute budget.
- **Lookup.** A 10-bit lookup table proves the 30-bit range decompositions
  that make the balance check an integer equality rather than an equality
  modulo p.

## Limitations

Each limitation is recorded in the paper's limitations section.

- **Argument soundness, not proof of knowledge.** The soundness theorem
  establishes that an accepting proof implies a witness exists for the exact
  relation; no extractor is constructed. It therefore does not by itself
  establish that a party who does not know a note's spending key cannot
  produce an accepting spend. Knowledge soundness, and with it a
  theft-resistance theorem for a deployed pool, is outside this release's
  claims.
- **Cross-deployment proof portability.** The statement binds the pool key,
  state, and public spend fields, but not cluster genesis or program
  identity; the identical proof is valid on any deployment that clones the
  statement-bound values. Economically linked deployments require a
  deployment-domain field absorbed into the transcript.
- **Compute-unit repricing.** Runtime CU pricing differs across clusters and
  changes over time. A repricing past the cap halts spends at these
  parameters — the executor's same-cluster preflight simulation fails closed
  before submission — and cannot admit invalid state.

## Verify the source

```bash
cargo fmt --all -- --check
cargo check -q -p aspis-xtask
cargo test --release -q -p aspis-prover --test spend_release_kat
cargo test --release -q -p aspis-xtask spend_release
cargo run -q -p aspis-prover \
  --example spend_soundness_epro_ledger -- --calculation-only
cargo-build-sbf --manifest-path programs/aspis-verifier/Cargo.toml
```

The release-certified proof and statement are committed at
`crates/aspis-prover/fixtures/`; the known-answer test verifies them
end-to-end through the production verifier. The release pipeline
(`cargo run --release -p aspis-xtask -- spend-release`) regenerates the
machine-checked certificate gates from fresh local-validator measurements.

## Paper

The [paper source](paper/aspis-spend/) states the exact relation,
transcript, and security reductions, with measured release values flowing
through `macros-generated.tex`. The PDF is rebuilt, frozen, and hash-pinned
when a release executes.

## Repository map

| Path | Contents |
| --- | --- |
| `crates/aspis-core/` | `no_std`, byte-exact host and SBF verifier core |
| `crates/aspis-prover/` | Prover, grinding, security calculators, and the release proof fixtures |
| `crates/aspis-statement/` | Shielded-spend relation and statement encoding |
| `programs/aspis-verifier/` | Wire format, dispatch, lifecycle, verification, and atomic state transition |
| `xtask/` | Release certification, measurement, and deployment execution |
| `paper/aspis-spend/` | Publication source and build instructions |
| `docs/` | Novelty search record and design history |
| `archive/` | Index of superseded and failed research retained in Git |

Earlier prototypes, rejected parameters, failed designs, and the research
measurement harness are preserved in immutable archive tags rather than
presented as the current release; the
[archive index](archive/README.md) lists them.

Licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE); citation
metadata is in [CITATION.cff](CITATION.cff).
