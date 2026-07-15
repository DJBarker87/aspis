# Aspis Spend day-of novelty re-scan

> **Dated snapshot.** This document records only the public-evidence search at
> the cutoff below. Its conditional deployment language is historical and
> must not be used as the current launch or chain-status record.

Search cutoff: `2026-07-13T20:35:53+01:00` (`Europe/London`,
`2026-07-13T19:35:53Z`).

Status: **the broad “first” claim is falsified by public prior art. The exact
mainnet/same-transaction conjunction was not falsified by this search, but it
is not yet quotable. A public, finalized mainnet-beta signature is a mandatory
remaining claim gate.**

Machine-readable companion:
[`novelty-rescan-2026-07-13.json`](novelty-rescan-2026-07-13.json).

```text
mainnet_signature_required_before_first_claim=true
mainnet_event_asserted_by_this_audit=false
first_claim_currently_allowed=false
```

This is a dated public-evidence search, not proof of an absolute historical
negative. Private code, unindexed deployments, and inaccurate or incomplete
project documentation can exist. Any release wording must therefore retain
both “to our knowledge” and the search date.

## 1. Exact object searched

The surviving candidate claim is the conjunction of all of the following:

1. the event is a successful, finalized **Solana mainnet-beta** transaction;
2. the transaction consumes a finalized, pre-uploaded proof account;
3. a Solana program itself verifies the complete transparent proof during
   that transaction, rather than trusting an off-chain verifier, committee,
   attestation, or recursively wrapped trusted-setup SNARK;
4. the proof is for a computationally hiding shielded-spend statement;
5. the same transaction atomically records the nullifier and mutates the pool
   state;
6. the complete verification/state-transition path consumes at most
   `1,400,000` CU;
7. the released parameters have a whole-ledger soundness lower bound exceeding
   100 bits in a **proven Johnson/MCA regime**, rather than an old
   capacity conjecture; and
8. the transaction, program identity, release certificate, proof identity,
   and relevant source are publicly checkable.

“One transaction” does not include proof-account creation or chunk-upload
transactions. Those operations must be disclosed as prior transactions; the
claim is about the atomic verification/state-transition transaction only.

The following broader formulations are not supported:

- “the first private payment on Solana”;
- “the first shielded pool on Solana”;
- “the first on-chain zero-knowledge verifier on Solana”;
- “the first transparent/STARK verifier on Solana”;
- “the first transparent shielded-payment project on Solana”; or
- “the entire proof lifecycle fits in one transaction.”

## 2. Search scope

The day-of scan used public web and repository indexes available at the cutoff.
It covered:

- GitHub repository and code search, followed by source inspection at pinned
  commits;
- IACR ePrint, arXiv, project papers, design documents, and whitepapers;
- official project sites and documentation;
- Solana mainnet-beta/devnet Explorer links and read-only RPC account checks;
- Google Patents and WIPO/PATENTSCOPE query families; and
- targeted searches for known Solana privacy and proof-verification projects.

Representative web/paper query families were:

```text
Solana transparent shielded spend STARK on-chain verifier nullifier one transaction
Solana privacy protocol shielded pool nullifier on-chain proof verification mainnet
Solana STARK verifier mainnet compute units transparent zero knowledge proof
Solana mainnet STARK shielded transfer on-chain verifier nullifier 1.4M CU
Solana mainnet transparent zero knowledge shielded spend STARK atomic transaction
site:github.com Solana shielded spend nullifier STARK verifier
site:eprint.iacr.org Solana shielded STARK privacy
site:arxiv.org Solana private payments STARK shielded
site:patents.google.com Solana STARK shielded transaction nullifier
```

Representative GitHub code-query families were:

```text
"stark" "nullifier" language:Rust
"fri" "nullifier" language:Rust
"Winterfell" "Solana" language:Rust
"shielded" "solana_program" language:Rust
"verify_stark" "solana" language:Rust
"transparent" "shielded" language:Rust
```

The targeted project pass included Protocol 01, solana-pqzk-fullchain,
Sombra, Hush, Cloak, Privacy Cash, Light Protocol, Elusiv, Otter Cash,
Poseidon Cash, Solana Confidential Transfer, Bonsol, SP1 Solana, Helius
Privacy, Styx, Zul, and Noctura. Search-result claims were not accepted on
their own when a primary repository, paper, official documentation page, or
chain record was available.

## 3. Result

### 3.1 The broad claim is falsified

Protocol 01 is decisive against the broad README-style formulation. Before
this scan date it publicly exposed a Solana devnet shielded pool and a custom
on-chain transparent STARK/FRI verifier for private-payment statements. Its
current pinned README labels both deployed programs as devnet programs and
describes proof submission to the on-chain FRI verifier:

- [Protocol 01 pinned README, devnet programs and verifier
  flow](https://github.com/IsSlashy/Protocol-01/blob/790dbff34ac96302fc6336d411fac14f683f5be9/README.md#L126-L154).

Separately, solana-pqzk-fullchain published and measured a direct Winterfell
STARK verifier on Solana devnet below the transaction cap. That work is not a
shielded spend, but it independently defeats any generic “first transparent
verifier on Solana” wording:

- [IACR ePrint 2025/1741](https://eprint.iacr.org/2025/1741);
- [solana-pqzk-fullchain pinned
  repository](https://github.com/pqzk-labs/solana-pqzk-fullchain/tree/2c888111e2f9c83252d9e019a99f19fe078e6428).

Accordingly, `README.md` must not lead with an unqualified first claim
whose distinguishing words are merely transparent, trusted-setup-free,
private-payment, or running as a Solana program.

### 3.2 The exact conjunction was not falsified

No public artifact found in the scan satisfied all eight conjuncts in
Section 1. This means the exact claim remains **unrefuted by this search**. It
does not establish an absolute first, and it does not authorize the claim
before the mainnet signature gate closes.

The strongest near-prior is Protocol 01. It misses the exact conjunction for
two independently sufficient reasons:

1. its published deployments are on devnet, not mainnet-beta; and
2. its proof verification and spend transition are split.

The pinned verifier source says `verify_deep_ali_phase2` must run after
`verify_stark_proof_v2` and was split because phase 1 already approaches or
exceeds Solana's 1.4M-CU limit:

- [Protocol 01 pinned phase-split
  source](https://github.com/IsSlashy/Protocol-01/blob/790dbff34ac96302fc6336d411fac14f683f5be9/programs/p01_stark_verifier/src/lib.rs#L222-L239).

The later shielded-transfer handler reads the already-set `verified` and
`deep_ali_verified` flags and only then records commitments and updates the
root:

- [Protocol 01 pinned transfer
  source](https://github.com/IsSlashy/Protocol-01/blob/790dbff34ac96302fc6336d411fac14f683f5be9/programs/zk_shielded/src/instructions/transfer_stark.rs#L169-L214).

The April phase-split commit is especially explicit: phase 1 had reached the
cap, DEEP-ALI moved to a dedicated phase-2 instruction, and transfer-circuit
phase 2 was measured separately:

- [Protocol 01 phase-split commit, 17 April
  2026](https://github.com/IsSlashy/Protocol-01/commit/2f08e830fcf3d0ac59e1ff4925a2b684b3557386).

At the cutoff, read-only RPC returned executable accounts for Protocol 01's
published verifier and pool IDs on devnet and `AccountNotFound` for both IDs
on mainnet-beta. This transient RPC observation corroborates, but does not
replace, the repository's own devnet label.

## 4. Nearest-prior comparison

| Candidate | What it establishes | Missing from the exact conjunction | Primary evidence |
|---|---|---|---|
| Protocol 01 | Transparent STARK/FRI shielded-payment programs deployed on Solana devnet | Mainnet-beta; complete proof verification and state mutation in one transaction; no published proven-Johnson/MCA whole-ledger certificate found | [README](https://github.com/IsSlashy/Protocol-01/blob/790dbff34ac96302fc6336d411fac14f683f5be9/README.md#L126-L154), [phase split](https://github.com/IsSlashy/Protocol-01/blob/790dbff34ac96302fc6336d411fac14f683f5be9/programs/p01_stark_verifier/src/lib.rs#L222-L239), [later transfer](https://github.com/IsSlashy/Protocol-01/blob/790dbff34ac96302fc6336d411fac14f683f5be9/programs/zk_shielded/src/instructions/transfer_stark.rs#L169-L214) |
| solana-pqzk-fullchain | Reproducible, direct on-chain Winterfell STARK verification on devnet, measured around 1.10M CU mean and below 1.19M maximum in the paper | Minimal affine-counter AIR, not a shielded spend; no atomic nullifier/pool mutation; devnet | [ePrint](https://eprint.iacr.org/2025/1741), [repository](https://github.com/pqzk-labs/solana-pqzk-fullchain/tree/2c888111e2f9c83252d9e019a99f19fe078e6428) |
| Cloak | Official site reports a live mainnet UTXO shielded pool, private transfers, and nullifiers; its published program ID was executable on mainnet-beta at the cutoff | Uses Groth16, so it is not transparent/trusted-setup-free | [official site](https://www.cloak.ag/), [mainnet program](https://explorer.solana.com/address/zh1eLd6rSphLejbFfJEneUwzHRfMKxgzrgkfwA6qRkW) |
| Privacy Cash | Mainnet shielded-pool precedent; its published program ID was executable on mainnet-beta at the cutoff | Published artifacts explicitly use a four-party trusted setup | [pinned trusted-setup record](https://github.com/Privacy-Cash/privacy-cash/blob/aa6818b76b23edcf05b8b9829a9cd900fdb1d241/artifacts/circuits/TRUSTED_SETUP.MD), [mainnet program](https://explorer.solana.com/address/9fhQBbumKEFuXtMBDw8AaQyAjCorLGJQiS3skWZdQyQD) |
| Sombra | Transparent STARK shielded-UTXO design with nullifiers and a single Solana finalization transaction | The final transaction commits a batch attestation and aggregated vote from attesting nodes; no direct Solana-program STARK verification is specified | [whitepaper](https://sombra.tech/whitepaper.pdf), retrieved SHA-256 `3e58a8c4675b6beae3be978c7e20e31a8b861635a7bc701461632a9c1c91cbd6` |
| Hush | Transparent Miden-STARK shielded-transfer system | The published flow has `zrchain` verify the proof and mark the nullifier before constructing/signing the Solana transaction | [official protocol page](https://hushprotocol.xyz/) |
| Solana Confidential Transfer | Native confidential token balances and transfer amounts | Account addresses remain public; it is not a note/nullifier shielded-spend construction | [Solana documentation](https://solana.com/docs/tokens/extensions/confidential-transfer) |
| Bonsol / RISC Zero route | General verifiable computation composable with Solana | The STARK is wrapped in Groth16 with a one-time trusted setup; Solana verifies the wrapper, not a transparent proof end-to-end | [Bonsol documentation](https://docs.bonsol.org/core-concepts/introduction) |
| Light Protocol published proving stack | Large deployed Solana ZK precedent | Published stack uses Gnark Groth16 and a two-phase trusted setup | [pinned setup repository](https://github.com/Lightprotocol/gnark-mt-setup/tree/85243034a19b98952440f5823f1a5ab139e52ca3) |

Sombra's retrieved PDF was 396,730 bytes. Protocol 01's retrieved design PDF
was 1,463,760 bytes with SHA-256
`cdc77b34136046fd1b89c85a85932d93ba37a24a8353b4ee41c036c11a0c8f60`.
These retrieval hashes pin the dynamic paper contents inspected on the search
date; the repository evidence above is pinned by commit.

## 5. Mainnet evidence gate

The novelty result must remain fail-closed until a public mainnet-beta
signature is inserted into the release record and independently checked. The
check must establish all of the following from the finalized transaction and
the pinned release artifacts:

- cluster is mainnet-beta and transaction status is successful/finalized;
- the invoked program ID corresponds to the released default SBF identity;
- the transaction consumes the finalized proof account bound to the released
  proof SHA-256;
- the program performs the complete proof verification in that transaction;
- the nullifier marker and pool-state mutation occur atomically in the same
  transaction;
- logged/observed CU is at most `1,400,000`; and
- the explorer/RPC link, program ID, proof-account address, release-certificate
  hash, proof hash, and source revision are public.

A local validator KAT or a release certificate, even when mined and
byte-identical to the intended SBF, is not a mainnet event. This audit records
no mainnet signature and asserts no such event.

## 6. Exact claim template after the gate closes

Only after Section 5 is satisfied, the following is the strongest wording
supported by this scan:

> To our knowledge, following a search completed 13 July 2026, Aspis provides
> the first publicly evidenced Solana mainnet-beta transaction in which a
> Solana program itself verifies a transparent, computationally hiding
> shielded-spend proof from a finalized pre-uploaded proof account and
> atomically records its nullifier and pool-state transition in that same
> transaction under the 1.4M-CU cap, with a whole-ledger soundness lower bound
> exceeding 100 bits in a proven Johnson/MCA regime.

The following scope note must appear adjacent to that sentence:

> Proof-account creation and chunk uploads occurred in prior transactions.
> Hiding is computational in the declared SHA-256
> programmable-random-oracle/EPRO and fixed public Proof-or-Abort channel
> model; this is not a statistical-HVZK or standard-model claim. The result is
> not an audit, a production-readiness claim, or a claim to be the first
> private-payment system on Solana.

Do not replace “to our knowledge” with an absolute article-only “the first.”
Do not remove the date. Do not generalize the object from the exact conjunction
to private payments, shielded pools, STARK verification, or transparent
verification separately.

## 7. Conclusion

The word “first” survives only inside the exact conjunction and only
conditionally. The day-of scan found no earlier public mainnet-beta event that
combines direct transparent proof verification, computational hiding, a real
shielded-spend statement, same-transaction nullifier/pool mutation, the
1.4M-CU cap, and a proven Johnson/MCA 100-bit-class ledger. It did find close
and important prior art for every broader subset of that sentence.

Until the public mainnet signature gate closes, the release may report the
measured implementation and dated novelty-search result, but it must not make
the first claim.
