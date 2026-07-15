# Aspis

Aspis is a shielded payment system whose spend proofs are verified directly
on Solana L1 — no trusted setup, no off-chain verifier. Solana caps every
transaction at 1.4 million compute units, which has kept transparent proof
verification on L1 out of reach. Aspis verifies a full shielded-spend proof,
advances the pool state, and records the nullifier in one finalized
mainnet-beta transaction at 1,343,749 CU:
[`4Er5afhx…E4q9Fo`](https://explorer.solana.com/tx/4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo?cluster=mainnet-beta).

[Paper](paper/profile23-mainnet-v1/profile23.pdf) ·
[Mainnet release](release/profile23-q18-g37-mainnet-v1/) ·
[Mainnet evidence](docs/profile23-mainnet-demo.md) ·
[Prepublication review](docs/reviews/profile23-prepublication-security-review.html)

## Transaction flow

![Proof upload, sealing, and one-transaction verification with atomic state transition](docs/assets/transaction-flow.svg)

1. The prover creates a transparent argument for the exact shielded-spend
   statement and uploads it in chunks to a program-owned account.
2. The account is sealed after its complete byte image is checked against the
   released proof.
3. One transaction verifies the sealed proof, closes and refunds that
   account, advances the pool, and creates the nullifier marker atomically.

## Mainnet result

The release — q18/g37, for its 18 queries per fold branch and 37-bit
batch-grinding parameter — was executed on Solana mainnet-beta on
14 July 2026:

| Released result | Value |
| --- | ---: |
| Finalized mainnet verification cost | 1,343,749 of 1,400,000 requested CU |
| Proof | 64,447 bytes |
| Conditional work-normalized soundness floor | 100.16 bits |
| Pairwise-witness hiding | 103.02 bits |
| Real-versus-simulator hiding | 104.02 bits |
| Maximum local verification cost | 1,340,803 CU |
| SBF program | 921,848 bytes |
| Finalized slot | `432933949` |
| Release certificate | [36/36 gates](results/stage2/profile23_one_transaction_release.json) |
| Mainnet proof-account refund | 0.449720400 SOL |
| Demo payer cost after refunds | 0.014883400 SOL |

[Official Explorer (mainnet-beta)](https://explorer.solana.com/tx/4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo?cluster=mainnet-beta) ·
[Solscan (mainnet)](https://solscan.io/tx/4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo?cluster=mainnet)

The transaction advanced the pool sequence from 0 to 1, created the canonical
nullifier marker, and refunded the proof account's 449,720,400 lamports. The
proof digest emitted by the program matches the released proof SHA-256,
`d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d`.
The official Solana mainnet RPC and an independent PublicNode endpoint agree
on the transaction, lifecycle records, and final accounts; the same signature
is absent on devnet and testnet. See the
[public reconciliation](results/stage2/profile23_mainnet_independent_rpc_reconciliation.json).
An archival replay also reconstructs the deployed SBF byte-for-byte from all
1,067 loader writes and decodes the exact tag-65 instruction; see the
[reconstruction result](results/stage2/profile23_mainnet_sbf_and_instruction_reconstruction.json)
and [stdlib-only replay script](tools/reconstruct_profile23_mainnet_sbf.py).

## Construction

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

## Verify the release

The versioned bundle freezes the proof, statement, SBF binary, certificates,
network evidence, paper, and SHA-256 manifest:

```bash
./release/profile23-q18-g37-mainnet-v1/verify.sh
```

Source-level checks:

```bash
NO_DNA=1 cargo fmt --all -- --check
NO_DNA=1 cargo check -q -p aspis-xtask
NO_DNA=1 cargo test --release -q -p aspis-xtask profile23_release
NO_DNA=1 cargo test -q -p aspis-xtask profile23_devnet
NO_DNA=1 cargo run -q -p aspis-prover \
  --example profile23_soundness_epro_ledger -- --calculation-only
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

## Limitations

- This is an unaudited research release with one independently reconciled
  mainnet execution.
- The one-transaction claim covers proof verification, the pool-state
  transition, nullifier creation, and the proof-account refund. Program
  deployment, pool and proof-account setup, the 68 chunk-upload
  transactions, and proof finalization are separate setup transactions.
- The relation is fixed: depth-20 Merkle membership, one input note, one
  output note.
- The security statements are argument soundness and computational hiding
  for the exact relation and declared random-oracle view; they do not
  assert knowledge soundness or a standard-model zero-knowledge result.

## Repository map

| Path | Contents |
| --- | --- |
| `crates/aspis-core/` | `no_std`, byte-exact host and SBF verifier core |
| `crates/aspis-prover/` | Prover, grinding, security calculators, and fixtures |
| `crates/aspis-statement/` | Shielded-spend relation and statement encoding |
| `programs/aspis-verifier/` | Upload, sealing, verification, refund, and atomic state transition |
| `xtask/` | Release generation, validator execution, and measurement tooling |
| `paper/profile23-mainnet-v1/` | Publication source, build instructions, and PDF |
| `release/profile23-q18-g37-mainnet-v1/` | Frozen mainnet publication bundle |
| `results/stage2/` | Machine-readable certificates and network records |
| `docs/` | Protocol, implementation, security, and deployment notes |
| `archive/` | Index of superseded and failed research retained in Git |

The `profile23` in file and certificate names is the internal working name
for this release. It stays in paths because the frozen SHA-256 manifests and
the on-chain evidence pin those exact filenames.

Earlier prototypes, rejected parameters, and failed designs are preserved in
the immutable
[`research-archive-2026-07-14`](https://github.com/DJBarker87/aspis/tree/research-archive-2026-07-14)
tag rather than presented as the current release.

Licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE); citation
metadata is in [CITATION.cff](CITATION.cff).
