# Aspis

Aspis is a transparent, trusted-setup-free argument system for a shielded-spend
relation on Solana. Profile 23 verifies a finalized, pre-uploaded proof and, in
the same transaction, advances the pool state, records the nullifier, and
refunds the proof-account rent.

[Paper](paper/profile23-mainnet-v1/profile23.pdf) ·
[Mainnet release](release/profile23-q18-g37-mainnet-v1/) ·
[Mainnet evidence](docs/profile23-mainnet-demo.md) ·
[Prepublication review](docs/reviews/profile23-prepublication-security-review.html) ·
[Devnet rehearsal](docs/profile23-devnet-rehearsal.md)

## Mainnet result

The exact q18/g37 release was executed successfully on Solana mainnet-beta on
14 July 2026. The verification transaction finalized at slot `432933949`,
consumed `1,343,749` of `1,400,000` requested compute units, advanced the pool
sequence from 0 to 1, created the canonical nullifier marker, and refunded the
proof account's `449,720,400` lamports.

[Official Explorer (mainnet-beta)](https://explorer.solana.com/tx/4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo?cluster=mainnet-beta) ·
[Solscan (mainnet)](https://solscan.io/tx/4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo?cluster=mainnet)

| Released result | Value |
| --- | ---: |
| Release certificate | [36/36 gates](results/stage2/profile23_one_transaction_release.json) |
| Query and grinding profile | q18, batch g37 |
| Conditional work-normalized soundness floor | 100.161449 bits |
| Pairwise-witness hiding | 103.024922 bits |
| Real-versus-simulator hiding | 104.024922 bits |
| Proof | 64,447 bytes |
| SBF program | 921,848 bytes |
| Maximum local verification cost | 1,340,803 CU |
| Finalized mainnet verification cost | 1,343,749 CU |
| Mainnet proof-account refund | 0.449720400 SOL |
| Demo payer cost after refunds | 0.014883400 SOL |

The proof digest emitted by the program matches the released proof SHA-256,
`d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d`.
The official Solana mainnet RPC and an independent PublicNode endpoint agree
on the transaction, lifecycle records, and final accounts; the same signature
is absent on devnet and testnet. See the
[public reconciliation](results/stage2/profile23_mainnet_independent_rpc_reconciliation.json).
An archival replay also reconstructs the deployed SBF byte-for-byte from all
1,067 loader writes and decodes the exact tag-65 instruction; see the
[reconstruction result](results/stage2/profile23_mainnet_sbf_and_instruction_reconstruction.json)
and [stdlib-only replay script](tools/reconstruct_profile23_mainnet_sbf.py).

Program deployment, proof upload, and proof finalization are setup operations;
the one-transaction claim concerns proof verification, state transition,
nullifier creation, and proof-account refund. The uploader uses 68 chunks in
five finality windows instead of waiting for every chunk sequentially.

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

## Protocol outline

1. The prover creates a transparent argument for the exact shielded-spend
   statement and uploads it to a program-owned account.
2. The account is sealed after its complete byte image is checked against the
   released proof.
3. Tag 65 verifies the sealed proof, closes and refunds that account, advances
   the pool, and creates the nullifier marker atomically.

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

Earlier prototypes, rejected parameters, and failed designs are preserved in
the immutable
[`research-archive-2026-07-14`](https://github.com/DJBarker87/zk/tree/research-archive-2026-07-14)
tag rather than presented as the current release.

Profile 23 is an unaudited research implementation with one independently
reconciled mainnet execution. Licensed under [MIT](LICENSE-MIT) or
[Apache-2.0](LICENSE-APACHE); citation metadata is in [CITATION.cff](CITATION.cff).
