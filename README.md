# Aspis

Aspis is a transparent, trusted-setup-free proof system for a shielded-spend
statement on Solana. Profile 23 verifies a finalized, pre-uploaded proof and
atomically advances pool state and records the nullifier in one transaction.

[Paper](paper/profile23/profile23.pdf) ·
[Frozen release](release/profile23-q18-g37/) ·
[Reproduction guide](paper/profile23/artifact/README.md) ·
[Devnet transaction](https://explorer.solana.com/tx/3ofPbzRkqMEJZCM9vwKz96rLqRFtSg4d1GyqqVBEbogtwzmJodsWb2f7V4X83BLvuPXFsT6Yyf87PC1ZbLf1R7bx?cluster=devnet)

## Profile 23 result

| Result | Value |
| --- | ---: |
| Release certificate | [35/35 gates](results/stage2/profile23_one_transaction_release.json) |
| Query and grinding profile | q18, batch g37 |
| Conservative soundness floor | 100.161449 bits |
| Pairwise-witness hiding | 103.024922 bits |
| Real-versus-simulator hiding | 104.024922 bits |
| Proof size | 66,367 bytes |
| SBF program size | 915,656 bytes |
| Maximum local verification cost | 1,314,386 of 1,400,000 CU |
| Local compute headroom | 85,614 CU |
| Finalized devnet cost | 1,314,332 CU |
| Finalized devnet slot | 476,231,605 |

The finalized devnet transaction verified the released proof, advanced the
pool sequence from 0 to 1, and created the nullifier marker. Its signed
simulation and landed execution both consumed 1,314,332 CU.

The recorded rehearsal used 104 serial proof uploads and spent 24 minutes 44
seconds in that upload interval. The current executor uses 960-byte chunks and
16-transaction finality windows: the same 66,367-byte proof requires 70 upload
transactions and five upload-finality waves. The full finalized account image
is still checked byte-for-byte before sealing.

## Verify the frozen release

The publication bundle contains the exact proof, public statement, SBF
binary, release certificate, finalized devnet evidence, paper, and their
SHA-256 identities.

```bash
./release/profile23-q18-g37/verify.sh
```

For source-level checks:

```bash
NO_DNA=1 cargo fmt --all -- --check
NO_DNA=1 cargo check -q -p aspis-xtask
NO_DNA=1 cargo test -q -p aspis-xtask profile23_devnet
NO_DNA=1 cargo run -q -p aspis-prover \
  --example profile23_soundness_epro_ledger -- --calculation-only
```

The [artifact guide](paper/profile23/artifact/README.md) documents complete
regeneration, local acceptance and mutation replay, fresh-proof generation,
and read-only recovery of the sealed proof from devnet.

## Repository map

| Path | Contents |
| --- | --- |
| `crates/aspis-core/` | `no_std`, byte-exact host and SBF verifier core |
| `crates/aspis-prover/` | Host prover, grinding, security calculators, and regression fixtures |
| `crates/aspis-statement/` | Shielded-spend relation and public statement encoding |
| `programs/aspis-verifier/` | Proof upload, sealing, verification, and atomic Solana state transition |
| `xtask/` | Release generation, validator execution, and measurement tooling |
| `paper/profile23/` | LaTeX paper, generated PDF, and artifact guide |
| `release/profile23-q18-g37/` | Self-contained frozen publication bundle |
| `results/stage2/` | Machine-readable release certificates and measurement records |
| `docs/` | Protocol, implementation, and security design notes |

## Design history

The default branch contains the current Profile 23 implementation and its
release evidence. Earlier prototypes, rejected parameter sets, measurements,
and failed design branches remain available in the
[`research-archive-2026-07-14`](https://github.com/DJBarker87/zk/tree/research-archive-2026-07-14)
tag. [Design history](docs/design-history.md) explains the split.

Profile 23 is a finalized devnet research release. It has not been audited or
deployed to mainnet.

Licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE). Citation
metadata is provided in [CITATION.cff](CITATION.cff).
