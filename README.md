# Aspis

[![Release integration](https://github.com/DJBarker87/aspis/actions/workflows/profile23-integration.yml/badge.svg)](https://github.com/DJBarker87/aspis/actions/workflows/profile23-integration.yml)

Aspis is a shielded payment system whose spend proofs are verified directly
on Solana L1 — no trusted setup, no off-chain verifier. Transparent proofs
are large, and Solana caps every transaction at 1.4 million compute units,
which has kept transparent proof verification on L1 out of reach. On
14 July 2026, Aspis verified a full
shielded-spend proof, advanced the pool state, and recorded the nullifier in
one finalized mainnet-beta transaction at 1,343,749 CU:
[`4Er5afhx…E4q9Fo`](https://explorer.solana.com/tx/4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo?cluster=mainnet-beta).

This is a research release, not an audit or a production service; the exact
claim, model, and limitations are in [Claim and scope](#claim-and-scope),
[Limitations](#limitations), and the paper.

[Paper](paper/profile23-mainnet-v1/profile23.pdf) ·
[Mainnet release](release/profile23-q18-g37-mainnet-v1/) ·
[Mainnet evidence](docs/profile23-mainnet-demo.md) ·
[Prepublication review](docs/reviews/profile23-prepublication-security-review.md)

## Headline numbers

The release — q18/g37, for its 18 queries per fold branch and 37-bit
batch-grinding parameter — was executed on Solana mainnet-beta on
14 July 2026:

| Result | Value |
| --- | ---: |
| One-transaction verification and state transition | 1,343,749 of the 1,400,000-CU cap ([cross-cluster CU reconciliation](docs/profile23-cu-reconciliation.md)) |
| Proof | 64,447 bytes |
| Soundness floor (work-normalized, proven Johnson/MCA regime) | 100.16 bits |
| Witness hiding | 103.02 bits pairwise, 104.02 bits versus simulator |
| End-to-end demo cost after refunds | 0.0149 SOL (≈ USD 1.15) |
| Release certificate | [36/36 gates](results/stage2/profile23_one_transaction_release.json) — machine-checked release conditions binding the proof, SBF binary, measurements, and manifests to each other |
| Finalized slot | `432933949` |

The soundness floor is work-normalized: an adversary limited to T
random-oracle queries, 1 ≤ T ≤ 2^128, falsely accepts with probability at
most T · 2^−100.16. The raw acceptance bound at large T is not booked as the
floor; the normalization and both interval endpoints are stated in the paper
and in the
[soundness ledger](docs/stage2-profile23-d-after-g-soundness-epro.md).

[Official Explorer (mainnet-beta)](https://explorer.solana.com/tx/4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo?cluster=mainnet-beta) ·
[Solscan (mainnet)](https://solscan.io/tx/4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo?cluster=mainnet)

The frozen bundle verifies offline (requires `jq`):

```bash
./release/profile23-q18-g37-mainnet-v1/verify.sh
```

The program log commits to
the released proof SHA-256; the official Solana RPC and an independent
PublicNode endpoint agree on the transaction, lifecycle records, and final
accounts; and an archival replay
([stdlib-only script](tools/reconstruct_profile23_mainnet_sbf.py))
reconstructs the deployed program byte-for-byte from the chain's own loader
history. After the spend, a sealed replay probe against the spent nullifier
was simulated and rejected with the exact expected double-spend error, then
closed with its rent refunded.

## Claim and scope

To our knowledge, following a public search completed 13 July 2026, this is
the first publicly evidenced Solana mainnet-beta transaction in which a
Solana program itself verifies a transparent, computationally hiding
shielded-spend proof from a finalized pre-uploaded proof account and
atomically records its nullifier and pool-state transition in that same
transaction under the 1.4M-CU cap, with a whole-ledger soundness lower bound
exceeding 100 bits in a proven Johnson/MCA regime
([search record](docs/profile23-novelty-rescan-2026-07-13.md)).
Scope: proof-account creation and chunk uploads occurred in prior
transactions; hiding is computational in the declared SHA-256
programmable-random-oracle/EPRO and fixed public Proof-or-Abort channel
model, not a statistical-HVZK or standard-model claim; and this is a research
release — not an audit, a production-readiness claim, or a claim to be the
first private-payment system on Solana.

## No trusted setup

Groth16 proofs are a few hundred bytes and cheap to verify, but their
soundness depends on a multi-party setup ceremony: a participant who
retained the ceremony's secret randomness could forge proofs, and a forged
spend inside a shielded pool is not detectable. The shielded pools that were
live on Solana mainnet at the July 2026 search date verify ceremony-based
Groth16 proofs or delegate proof verification to off-chain systems
([comparison table](docs/profile23-novelty-rescan-2026-07-13.md)).

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

### Operational envelope

The complete spend lifecycle, measured on mainnet:

| Quantity | Value | Source |
| --- | --- | --- |
| Setup transactions | 72 total: 70 per spend (proof-account create, 68 chunk uploads, finalize) plus 2 per pool (create, initialize) | [mainnet evidence](release/profile23-q18-g37-mainnet-v1/evidence/mainnet-execution.raw.public.json), measured |
| Setup-to-finalized-verification span | 449 slots, about 3 minutes | slots `432933500` to `432933949`, measured |
| Proof-account rent held until the spend refunds it | 0.4497 SOL (449,720,400 lamports) | [demo record](docs/profile23-mainnet-demo.md), measured |
| Demo-payer cost after refunds, calm network, base fees only | 0.0149 SOL | [cost ledger](docs/profile23-demo-cost-refund.md), measured |
| Spend ordering within one pool | strictly sequential; each proof binds the pool's current sequence number | statement encoding, paper §relation |
| Proof-generation wall-clock and hardware | not part of the published record | — |

The 0.0149 SOL figure was measured at base fees on an uncongested network.
Priority fees are priced per requested compute unit, so congestion raises
this transaction's landing cost more than a small transaction's.

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

Each limitation is recorded in the paper's limitations section or the
[prepublication review](docs/reviews/profile23-prepublication-security-review.md).

- **Argument soundness, not proof of knowledge.** The soundness theorem
  establishes that an accepting proof implies a witness exists for the exact
  relation; no extractor is constructed. It therefore does not by itself
  establish that a party who does not know a note's spending key cannot
  produce an accepting spend. Knowledge soundness, and with it a
  theft-resistance theorem for a deployed pool, is outside this release's
  claims.
- **Cross-deployment proof portability (review R-02).** The statement binds
  the pool key, state, and public spend fields, but not cluster genesis or
  program identity; the identical proof is valid on any deployment that
  clones the statement-bound values. Economically linked deployments require
  a deployment-domain field absorbed into the transcript, a new proof, and a
  new release certificate.
- **Compute-unit repricing.** Runtime CU pricing differs across clusters and
  changes over time; the identical transaction cost 3,000 CU more on mainnet
  than on devnet. Current headroom is 56,251 CU (4.0% of the cap); a
  repricing past the cap would halt spends at these parameters, not admit
  invalid state. See the
  [CU reconciliation note](docs/profile23-cu-reconciliation.md).
- **Open review findings.** R-05 (no independent audit or fuzz campaign) and
  R-07 (host-tooling dependency advisories) are open; the review's
  disposition is publication-ready as a research result, not cleared as a
  value-bearing service.

## Verify the release

The versioned bundle freezes the proof, statement, SBF binary, certificates,
network evidence, paper, and SHA-256 manifest:

```bash
./release/profile23-q18-g37-mainnet-v1/verify.sh
```

Source-level checks:

```bash
cargo fmt --all -- --check
cargo check -q -p aspis-xtask
cargo test --release -q -p aspis-xtask profile23_release
cargo test -q -p aspis-xtask profile23_devnet
cargo run -q -p aspis-prover \
  --example profile23_soundness_epro_ledger -- --calculation-only
```

The deployed SBF binary rebuilds byte-for-byte from this tree on Solana
platform-tools v1.48:

```bash
cargo-build-sbf --manifest-path programs/aspis-verifier/Cargo.toml
shasum -a 256 target/deploy/aspis_verifier.so
# 97c45a9abef97607a2fc6ed245829210046b234044b6738599d2bce0c367d04a
```

The optional live chain reconstruction uses archival JSON-RPC history and is
network-rate-limited independently of proof generation:

```bash
python3 tools/reconstruct_profile23_mainnet_sbf.py \
  --output /tmp/profile23-mainnet-reconstruction.json \
  --compare-substantive \
  results/stage2/profile23_mainnet_sbf_and_instruction_reconstruction.json
```

## Paper

[The paper](paper/profile23-mainnet-v1/profile23.pdf) states the exact
relation, transcript, and security reductions. Its abstract:

> This paper presents [Aspis], a transparent argument for a depth-20,
> one-input/one-output shielded-spend relation together with a Solana program
> that verifies the argument and atomically records the corresponding
> nullifier and pool-state transition. The accepting instruction consumes a
> finalized, pre-uploaded proof account; proof-account creation, chunk
> upload, and finalization are separate setup transactions. The
> polynomial-commitment layer is a custom circle-domain, WHIR-style
> multilinear protocol at rate 1/512, with 18 sampled query fibers and
> batch-work parameter g = 37. Under the stated finite-parameter and
> boundary-state-restoration premises, the frozen event ledger and its
> 32-boundary Fiat–Shamir reduction give a conservative 100.161-bit floor
> for work-normalized false acceptance per random-oracle query. Under the
> stated affine-image premise, an explicit simulator gives 104.024 bits for
> a real view versus simulation and 103.024 bits for pairwise witness hiding
> in the declared programmable-SHA-256 random-oracle, fixed Proof-or-Abort
> view. The pinned implementation artifact contains a 64,447-byte proof and
> a 921,848-byte Solana bytecode format (SBF) binary. A finalized
> mainnet-beta transaction verified that proof, closed and refunded its
> proof account, advanced the pool sequence, and created the nullifier
> marker in one atomic transition. It consumed 1,343,749 of the 1,400,000
> requested compute units. Program deployment, pool and proof-account setup,
> proof upload, and proof finalization were separate transactions. The
> security statements are argument soundness and computational hiding for
> the exact relation and declared view; they do not assert knowledge
> soundness or a standard-model zero-knowledge result.

## Repository map

| Path | Contents |
| --- | --- |
| `crates/aspis-core/` | `no_std`, byte-exact host and SBF verifier core |
| `crates/aspis-prover/` | Prover, grinding, security calculators, and fixtures |
| `crates/aspis-statement/` | Shielded-spend relation and statement encoding |
| `programs/aspis-verifier/` | Upload, sealing, verification, refund, and atomic state transition |
| `xtask/` | Release generation, deployment execution, and evidence tooling |
| `paper/profile23-mainnet-v1/` | Publication source, build instructions, and PDF |
| `release/profile23-q18-g37-mainnet-v1/` | Frozen mainnet publication bundle |
| `results/stage2/` | Machine-readable certificates and network records |
| `docs/` | Protocol, implementation, security, and deployment notes |
| `archive/` | Index of superseded and failed research retained in Git |

The `profile23` in file and certificate names is the internal working name
for this release. It stays in paths because the frozen SHA-256 manifests and
the on-chain evidence pin those exact filenames.

Earlier prototypes, rejected parameters, failed designs, and the diagnostic
measurement harness are preserved in immutable archive tags rather than
presented as the current release; the
[archive index](archive/README.md) lists them.

Licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE); citation
metadata is in [CITATION.cff](CITATION.cff).
