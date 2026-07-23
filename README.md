# Aspis

[![Spend integration](https://github.com/DJBarker87/aspis/actions/workflows/spend-integration.yml/badge.svg)](https://github.com/DJBarker87/aspis/actions/workflows/spend-integration.yml)

Aspis demonstrates that a transparent, trusted-setup-free proof for a
shielded-spend state transition can be verified entirely on Solana L1 inside
its 1.4 million compute-unit limit.

On 2026-07-16 one finalized mainnet-beta transaction verified a 65,407-byte
shielded-spend proof, advanced the pool state, and recorded the nullifier in
one atomic step, at 1,344,003 of the 1,400,000-CU cap:
[`3G1vogg…sRPFcv`](https://explorer.solana.com/tx/3G1voggszvDMGi5PbGM1kuEMYKvh2TNMbH6hHHwndUdRQJNT7ehRFpQpksxLnx5tp2xkS5jGi359rVXk42sRPFcv?cluster=mainnet-beta).
The program was a disposable deployment and was closed after the run
([evidence](docs/mainnet-demo.md)).

The released construction is the spend-verification primitive: one input, one
output, a same-path leaf replacement in a depth-20 tree, and an atomic pool and
nullifier transition. It establishes the on-chain feasibility result; deposit,
wallet, growing-anonymity-set, and multi-input/output protocols are separate
work.

The code, proof artefacts, measurements, formal development, failed approaches,
and security argument are public so the result can be reproduced and
challenged. The exact model is in the [paper](paper/aspis-spend/) and
[Limitations](#limitations). The
[novelty re-scan](docs/novelty-rescan-2026-07-13.md) is a dated public-evidence
search for the claim shape.

The starting point was Jotaro Yano's measurement study
([ePrint 2025/1741](https://eprint.iacr.org/2025/1741),
[solana-pqzk-fullchain](https://github.com/pqzk-labs/solana-pqzk-fullchain)),
which verified a minimal Winterfell STARK inside one Solana transaction on
devnet. This repository began as a cost model calibrated against that
verifier, and the first commit carries its measured profile. The work then
asked whether the same budget could hold a real spend statement. The
construction that answers it shares no components with his prototype, but the
direction came from his paper.

This is a solo project built with heavy AI assistance. The evidence is the
checked code, frozen artefacts, Lean proofs, and reproducible measurements—not
the development process.

## Current status

Aspis now has two clearly separated release lines:

| Track | Status | Runtime result |
| --- | --- | ---: |
| q18/g37, tag 65 | Executed and finalized on mainnet-beta on 2026-07-16 | 1,344,003 CU |
| V5, tag 67 | Production-default, provenance-bound deployment candidate; not yet deployed | universal accepted-grammar ceiling 1,353,616 CU |

The q18/g37 release is the published mainnet feasibility result. V5 is the
current verifier architecture: its default SBF is 1,258,496 bytes, SHA-256
`4cf3c1d5…edf40`, and has 46,384 CU of conservative headroom. Its code,
source-authentic formal closure, provenance, and CU evidence are recorded in
the [V5 production preflight](release/preflight/v5-production-freeze.md).

## Release numbers

| Result | Value |
| --- | ---: |
| One-transaction verification and state transition | 1,344,003 of the 1,400,000-CU cap |
| Proof | 65,407 bytes |
| Soundness floor (work-normalized, proven Johnson/MCA regime) | ~100 bits |
| Zero knowledge (conditional computational, programmable ROM, declared view) | ~104-bit real-vs-simulator floor; ~103-bit pairwise witness-indistinguishability |
| Finalized slot | `433219840` |

The soundness floor is a per-query figure: after the Fiat–Shamir reduction and
a conservative whole-ledger factor of three, the false-acceptance probability
is at most 2^−100.16 per random-oracle query. Like any grinding-based bound the
cumulative advantage grows with the query budget and goes vacuous past roughly
2^105 queries. The full event ledger, the per-budget table, and the exact
reduction are in the [paper](paper/aspis-spend/), recomputed by
`spend_soundness_epro_ledger`.

The floor is argument soundness: a satisfying witness exists. The
theft-resistance corollary additionally uses a named round-by-round knowledge
premise. The paper keeps the proved soundness statement and that extra
knowledge assumption separate.

## No trusted setup

Groth16 proofs are a few hundred bytes and cheap to verify, but their
soundness depends on a multi-party setup ceremony: a participant who retained
the ceremony's secret randomness could forge proofs, and a forged spend inside
a shielded pool is not detectable. Shielded pools on Solana today verify
ceremony-based Groth16 proofs or delegate proof verification to off-chain
systems ([comparison record](docs/novelty-rescan-2026-07-13.md)).

Aspis has no ceremony. Its parameters are public constants, and its security
reductions rest on the hash assumptions stated in the paper, a concrete
Poseidon2 assumption and SHA-256 modelled as a random oracle, rather than on a
reference string with a trapdoor. The cost is proof size: 65,407 bytes against
a few hundred for Groth16. Closing that size gap on-chain is what the
transaction design below is for.

## One transaction

![Proof upload, sealing, and one-transaction verification with atomic state transition](docs/assets/transaction-flow.svg)

A 65,407-byte proof exceeds Solana's 1,232-byte transaction packet limit, so
it is uploaded once and verified in place:

1. The prover uploads the proof in 69 chunks to a program-owned account.
2. The account is sealed after its complete byte image is checked against
   the released proof digest.
3. One transaction then verifies the sealed proof, advances the pool,
   records the nullifier, and refunds the proof account, atomically. If any
   step fails, no state changes.

A spend therefore costs 71 setup transactions (proof-account create, 69 chunk
uploads, finalize) before the verification transaction, plus 2 per pool
(create, initialize). The proof account's rent is held from creation until the
verification transaction refunds it.

### Throughput and scaling

Spends within one pool are strictly sequential. Each proof is ground against
the pool's current sequence number, and the pool account is writable-locked
during the verification transaction, so one pool processes one spend at a time
and each spend needs a freshly ground proof against the state the previous
spend produced. Per-pool throughput is bounded by prove-and-grind latency, not
by Solana. Horizontal scaling is by running multiple independent pools, which
fragments the anonymity set across pools, so the privacy of a spend is set by
the pool it lands in, not by the system as a whole. A shared cross-pool state
structure (a nullifier queue or tree in place of one PDA per spend) is not part
of this release.

Each spend also creates one canonical nullifier PDA that persists on-chain at
its rent minimum, so nullifier storage grows linearly with the number of
spends. The 1,344,003-CU verification leaves 55,997 CU of headroom under the
cap (about 4%), so the parameters do not survive a runtime compute-unit
repricing that raises this workload past the cap (see
[Limitations](#limitations)).

## Construction

The parameters are chosen to fit complete verification under Solana's
compute-unit cap. The commitment layer is WHIR-style rather than FRI because
the cap prices verifier queries, not prover time.

- **Field.** M31 (p = 2³¹ − 1) with its circle group as the evaluation
  domain. Mersenne arithmetic is cheap on the 32-bit SBF target, and the
  degree-four extension QM31 supplies sampling soundness.
- **Hash.** Poseidon2 over M31 (width 16) for note commitments, nullifiers,
  and owner derivation, algebraic and so cheap inside the relation. SHA-256 is
  the Fiat–Shamir oracle because SBF exposes a native SHA-256 syscall.
- **Commitment.** A custom circle-domain, WHIR-style multilinear PCS: batched
  multilinear evaluation with four arity-four folds. It is not an invocation of
  an unmodified WHIR parameter set.
- **Rate.** 1/512 (2¹⁰ message rows to 2¹⁹ circle symbols). High blowup buys
  per-query soundness, so few queries are needed, which is what the
  compute-unit cap rewards.
- **Queries.** q = 18 per branch, sampled without replacement, with three
  query branches per attempt.
- **Grinding.** 37-bit batch work, per-fold work of 34/33/30/25 bits, and
  32-bit final work. Grinding supplies soundness bits that additional queries
  could not fit in the compute budget.
- **Lookup.** A 10-bit lookup table proves the 30-bit range decompositions
  that make the balance check an integer equality rather than an equality
  modulo p.

## Machine-checked evidence

The repository contains two complementary formal layers.

- [`AspisFormal/`](AspisFormal/) is the maintained Lean 4 development. For the
  q18/g37 construction it kernel-checks the value-conservation and relation
  core, finite soundness ledger, work-normalized endpoint, circle-group and
  fibre facts, hiding lemmas, Poseidon2 known-answer bindings, and the
  theft-resistance implication from its explicitly cited interfaces.
- [`aeneas-verif/`](aeneas-verif/) connects the current V5 Rust implementation
  to maintained Lean models through pinned Charon/Aeneas extraction. Its final
  capstone joins Components A, B, and C—including the public Component-C
  output—with the Tag-67 wire and six-step work verifier.

The final V5 theorem has one implementation boundary: the actual transcript
hash application must equal the maintained `HashFn` applied to
`DOM_GRIND || nonce_le64`. Parser, projection, digest-predicate, and six-step
correspondence are theorem conclusions rather than assumptions. The audited
capstones use only Lean's standard `{propext, Classical.choice, Quot.sound}`
base. Published PCS, Fiat–Shamir, extractor, and cryptographic hash-security
results remain cited assumptions, as they should.

## Limitations

The limits define the next engineering and research steps; the paper gives the
full statements.

- **Knowledge.** The base theorem proves argument soundness. Theft resistance
  additionally uses the stated round-by-round extractor premise.
- **Application scope.** The q18/g37 release is one input, one output, one
  sequential pool, and a same-path replacement. It has no deposit or append
  path, so the demonstrated anonymity set was one.
- **Privacy scope.** The simulator covers the declared proof-and-execution view
  in the programmable SHA-256 random-oracle model. Fee-payer linkage,
  transaction graphs, network metadata, timing, and physical side channels are
  different privacy layers.
- **Deployment identity.** Statements bind the runtime program ID and an
  operator-selected domain tag. The executor checks the cluster genesis;
  including genesis directly in the statement would make that binding
  self-contained.
- **Operations.** Proof upload takes 71 preparatory transactions, one pool is
  sequential, nullifier storage grows linearly, and a CU repricing beyond the
  measured headroom would require new parameters.
- **Assurance.** The repository includes internal review, formal proofs,
  independent checkers, and frozen mainnet evidence. Independent cryptographic
  and Solana review and a published coverage-guided fuzz campaign remain the
  next assurance milestones.

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

## Verify the release

The finalized mainnet-beta execution is frozen in an offline-verifiable
bundle. From the repository root:

```bash
./release/aspis-spend-q18-g37-mainnet-v1/verify.sh
```

It needs only `jq` and `sha256sum` or `shasum`, runs fully offline, and checks
every published byte against `SHA256SUMS` and `manifest.json`, the proof and
SBF container magics, the release-certificate gates, and the finalized on-chain
signature, slot, and compute units.

## Paper

The [paper source](paper/aspis-spend/) and adjacent PDF are the living
manuscript. The immutable q18/g37 publication PDF is
[`release/aspis-spend-q18-g37-mainnet-v1/paper/aspis-spend.pdf`](release/aspis-spend-q18-g37-mainnet-v1/paper/aspis-spend.pdf),
identical to the PDF attached to the GitHub Release. This keeps the executed
release record fixed while allowing the manuscript to document later formal
work.

## Repository map

Concept-to-file navigation: [docs/code-map.md](docs/code-map.md). Each crate
carries a README naming its production entry points.

| Path | Contents |
| --- | --- |
| `.cargo/` | Reproducible Cargo aliases and build configuration |
| `.github/` | CI for Rust, release bindings, and Lean kernel checks |
| `AspisFormal/` | Maintained Lean 4 formalisation and proof-status table |
| `aeneas-verif/` | Curated Rust-to-Lean extraction proofs and V5 capstones |
| `crates/aspis-core/` | `no_std`, byte-exact host and SBF verifier core |
| `crates/aspis-prover/` | Prover, grinding, security calculators, and the release proof fixtures |
| `crates/aspis-statement/` | Shielded-spend relation and statement encoding |
| `programs/aspis-verifier/` | Wire format, dispatch, lifecycle, verification, and atomic state transition |
| `xtask/` | Release certification, measurement, and deployment execution |
| `paper/aspis-spend/` | Publication source and build instructions |
| `docs/` | Novelty search record and design history |
| `manifests/` | Machine-readable parameter and release bindings |
| `reference/` | Compact independent reference material |
| `release/` | Immutable mainnet bundle and V5 production preflight |
| `results/` | Curated runtime measurements and final V5 evidence |
| `tools/` | Independent checkers and formal/evidence utilities |
| `archive/` | Index of superseded and failed research retained in Git |

Earlier prototypes, rejected parameters, failed designs, and the research
measurement harness are preserved in immutable archive tags rather than
presented as the current release; the [archive index](archive/README.md) lists
them.

Licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE); citation
metadata is in [CITATION.cff](CITATION.cff).
