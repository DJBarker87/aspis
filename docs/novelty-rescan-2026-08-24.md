# Aspis Spend pre-publication novelty re-scan

> **Dated snapshot.** This document records only the public-evidence search at
> the cutoff below. It supersedes the search date of
> [`novelty-rescan-2026-07-13.md`](novelty-rescan-2026-07-13.md) but does not
> retract it; that document remains the record of its own cutoff.

Search cutoff: `2026-08-24T20:58:01+01:00` (`Europe/London`,
`2026-08-24T19:58:01Z`).

Status: **the broad "first" claim remains falsified by public prior art. The
exact conjunction was not falsified by this search. The mainnet-signature gate
that blocked the claim on 13 July is now closed by the recorded mainnet-beta
transaction, so the claim is quotable under the template in Section 7.**

Machine-readable companion:
[`novelty-rescan-2026-08-24.json`](novelty-rescan-2026-08-24.json).

```text
mainnet_signature_required_before_first_claim=true
mainnet_signature_recorded=true
mainnet_event_asserted_by_this_audit=false
first_claim_currently_allowed=true
```

This is a dated public-evidence search, not proof of an absolute historical
negative. Private code, unindexed deployments, and inaccurate or incomplete
project documentation can exist. Any release wording must therefore retain both
"to our knowledge" and the search date.

## 1. Exact object searched

The eight-part conjunction is unchanged from
[`novelty-rescan-2026-07-13.md` §1](novelty-rescan-2026-07-13.md). It is
restated here only by reference. The broader formulations rejected in that
document remain rejected, and this scan found no evidence that would revive any
of them.

## 2. Search scope

This scan re-ran the web, paper, repository, and patent query families recorded
in [`novelty-rescan-2026-07-13.md` §2](novelty-rescan-2026-07-13.md), restricted
to material published or modified after `2026-07-13T19:35:53Z`, and re-checked
the near-prior candidates named in that document.

GitHub code-query families were re-run through the authenticated code-search
API rather than the web index. The patent families returned no Solana-specific
transparent-verifier filing.

Targeted re-checks: Protocol 01, solana-pqzk-fullchain, Sombra, Hush, Cloak,
Privacy Cash, Light Protocol, Elusiv, Otter Cash, Poseidon Cash, Solana
Confidential Transfer, Bonsol, SP1 Solana, Helius Privacy, Styx, Zul, Noctura.
Candidates newly added to the target list at this cutoff: Arcium/Umbra,
wienerlabs/mosaic, Zera Labs, HFIPay.

## 3. Result

### 3.1 The broad claim remains falsified

Nothing at this cutoff weakens the 13 July finding. Protocol 01 continues to
expose a transparent STARK/FRI shielded-payment verifier and pool on Solana
devnet, and solana-pqzk-fullchain's measured devnet Winterfell verifier
continues to defeat any generic "first transparent verifier on Solana" wording.

### 3.2 The exact conjunction was not falsified

No public artifact found in this scan satisfies all eight conjuncts. The
strongest near-prior is still Protocol 01, and it still misses for the same two
independently sufficient reasons: its deployments are devnet, and its proof
verification is split from its state transition.

Protocol 01's repository was pushed on 2026-08-23, one day before this cutoff,
and its roadmap entry `Mainnet deployment` is unchecked. Its README states that
the coset low-degree-extension verifier was redeployed on devnet on 2026-08-04
and measured at 809,812 CU for an accepted honest proof, that "no audited
soundness figure is claimed," and that the shipped web app, APK, and
`@protocol-01/stark-prover@0.1.2` emit pre-coset proof blobs the deployed chain
verifier rejects. The project describes itself as a privacy layer for Solana
using both SNARKs and STARKs.

### 3.3 The mainnet gate recorded in the 13 July scan is closed

The 13 July document made the claim conditional on a public finalized
mainnet-beta signature. That gate is closed by the recorded transaction
[`3G1vogg…42sRPFcv`](https://explorer.solana.com/tx/3G1voggszvDMGi5PbGM1kuEMYKvh2TNMbH6hHHwndUdRQJNT7ehRFpQpksxLnx5tp2xkS5jGi359rVXk42sRPFcv?cluster=mainnet-beta)
at finalized slot `433219840` on 2026-07-16, three days after that scan closed,
with evidence in
[`release/aspis-spend-q18-g37-mainnet-v1/`](../release/aspis-spend-q18-g37-mainnet-v1/)
and [`docs/mainnet-demo.md`](mainnet-demo.md). The later V5/tag-67 line
finalized separately at slot `435019536`.

This audit records that the artifacts exist and are internally consistent. It
does not itself re-verify chain finality; that check is
[`release/aspis-v5-tag67-mainnet-v1/verify.sh`](../release/aspis-v5-tag67-mainnet-v1/)
and `tools/check_release_facts.py`.

## 4. Delta since 13 July

| Candidate | Date | Bearing on the conjunction |
|---|---|---|
| [Protocol 01](https://github.com/IsSlashy/Protocol-01) | pushed 2026-08-23 | Unchanged as a near-prior. Devnet only; `Mainnet deployment` unchecked; verification and state transition still split; deployed clients desynchronised from the redeployed verifier. |
| [HFIPay](https://arxiv.org/html/2603.26970v2) | arXiv 2603.26970v2, 21 Jun 2026 | New. Circle STARK plus Solana, but reports no mainnet deployment, states the Circle STARK proof is "too large for direct per-transaction submission and is intended for per-block aggregation," uses Groth16 as the on-chain path, and uses per-intent blinded bindings rather than nullifiers. Does not meet conjuncts 1, 3, or 5. |
| [Arcium mainnet alpha / Umbra](https://www.theblock.co/post/387564/arcium-launches-privacy-preserving-mainnet-alpha-on-solana-as-umbra-debuts-shielded-finance-layer) | Mainnet alpha Feb 2026; public Mar 2026 | Live shielded transfers on Solana mainnet, built on encrypted computation (MPC), not on-chain verification of a transparent proof. Does not meet conjunct 3. Absent from the 13 July target list; added here. |
| [wienerlabs/mosaic](https://github.com/wienerlabs/mosaic) | pushed 2026-06-08 | On-chain verifier library for Solana covering Groth16, PLONK, FRI-STARK, and Nova. Devnet integration tests, mainnet-ladder roadmap. Not a shielded spend and no nullifier or pool mutation. Does not meet conjuncts 1, 4, or 5. **Predates the 13 July cutoff and was missed by that scan** (see Section 5). |
| [Zera Labs](https://zeralabs.org/) | checked 2026-08-24 | Solana privacy protocol described as using zk-SNARKs with Pedersen commitments; wallet listed as "coming soon." Not transparent; no mainnet verification evidence found. Does not meet conjunct 3. |
| [arXiv 2511.00415](https://arxiv.org/html/2511.00415) | 23 Oct 2025 | Theory paper on ZK architecture for Solana. Implementation-agnostic; names no deployed system meeting the conjunction. Citable as related work, not prior art. |
| [Starknet STRK20 / v0.14.2](https://www.starknet.io/blog/starknet-v0-14-2-the-privacy-engine-arrives/) | 2026 | Not Solana. Related work only. |
| Fantasma, Hegemon, zkSealevel, postera, dregg | 2026 code-search hits | STARK or nullifier code outside the object: post-quantum identity, a separate chain, devnet validator-state proofs, and unwired scaffolding respectively. None meet the conjunction. |

## 5. Recorded miss in the 13 July scan

`wienerlabs/mosaic` was last pushed on 2026-06-08 and was therefore public and
indexable at the 13 July cutoff, but does not appear in that document. It does
not falsify the conjunction, and its omission does not change the 13 July
result. It is recorded here because the accuracy of a dated negative search
depends on disclosing known coverage failures.

The 13 July scan located it under none of its six GitHub code-query families.
This scan found it through the authenticated code-search API on the query
`"Winterfell" solana language:Rust`.

## 6. Out-of-scope finding: Poseidon2 cryptanalysis

This is not a novelty finding and does not bear on Section 3. It is recorded
here because it was surfaced by the same pre-publication search and it touches
[`docs/assumptions-ledger.md`](assumptions-ledger.md).

A sustained algebraic-cryptanalysis campaign against Poseidon and Poseidon2 ran
through 2026: [ePrint 2026/150](https://eprint.iacr.org/2026/150),
[2026/306](https://eprint.iacr.org/2026/306),
[2026/967](https://eprint.iacr.org/2026/967),
[2026/1579](https://eprint.iacr.org/2026/1579), and
[2026/1692](https://eprint.iacr.org/2026/1692) of 15 August 2026. The Ethereum
Foundation has abandoned Poseidon for L1 in favour of SHA or BLAKE.

Aspis uses Poseidon2 over Mersenne31 at width 16, `alpha = 5`, 8 full and 14
partial rounds, with constants copied from `p3-mersenne-31 0.6.1`
([`crates/aspis-statement/src/poseidon2.rs`](../crates/aspis-statement/src/poseidon2.rs)).
On the published evidence that parameter set is not broken. ePrint 2026/306 §6
states that "the 128-bit security of Poseidon2(b) with respect to preimage and
collision attacks does not appear to be compromised," and that the attack
complexity "surpasses 2^128 whenever `alpha >= 3`." §6.1 adds that "for all
Poseidon instances we found no parameter set failed to meet its asserted
128-bit security level."

Four qualifications constrain how this may be written up:

1. ePrint 2026/306 §6.1 states that Plonky3 "recommended round numbers for
   `(n,t) = (64,16)` [...] were not considered by the designers of Poseidon and
   are also more susceptible to improved round skips." Aspis is `n = 32`, not
   `n = 64`, so the literal instance is not ours, but the criticism is directed
   at the provenance of our constants.
2. The two figures circulating in secondary coverage do not apply to this
   parameter set and must not be cited as though they do. The factor-`2^106`
   collision improvement is for Poseidon2b over binary fields at
   `alpha = 7, R_P = 15`. The `2^164` to `2^126` preimage revision is for a
   31-bit instance at `alpha = 3`. Aspis is `alpha = 5`.
3. No published complexity estimate was found for the exact Aspis
   configuration.
4. A round-count increase at `t = 16` from 8 full and 14 partial to 10 full and
   17 partial is attributed to Koschatko (TU Graz) in secondary coverage, for
   `d = 7`. Aspis is exactly 8 full and 14 partial at `t = 16`. This attribution
   was not confirmed against a primary source at this cutoff; the Poseidon
   initiative publishes no updated production guidance.

ePrint 2026/306 §6.1 gives an eight-step procedure for computing the best round
skip for an individual parameter set. Running it against
`(M31, t = 16, alpha = 5, R_F = 8, R_P = 14)` and publishing the resulting
ideal-degree bound would convert the Poseidon2 row of the assumptions ledger
from a named interface into a quantified one. That work is not done and is not
claimed here.

## 7. Exact claim template

The mainnet gate is closed, so the following wording is supported by this scan.
Only the date differs from the 13 July template:

> To our knowledge, following a search completed 24 August 2026, Aspis provides
> the first publicly evidenced Solana mainnet-beta transaction in which a
> Solana program itself verifies a transparent, computationally hiding
> shielded-spend proof from a finalized pre-uploaded proof account and
> atomically records its nullifier and pool-state transition in that same
> transaction under the 1.4M-CU cap, with a whole-ledger soundness lower bound
> exceeding 100 bits in a proven Johnson/MCA regime.

The scope note from
[`novelty-rescan-2026-07-13.md` §6](novelty-rescan-2026-07-13.md) must appear
adjacent to that sentence, unchanged.

Do not replace "to our knowledge" with an absolute article-only "the first." Do
not remove the date. Do not generalize the object from the exact conjunction to
private payments, shielded pools, STARK verification, or transparent
verification separately.

## 8. Limitations

- This is a dated public-evidence search, not an absolute historical negative.
- Chain state was not re-queried by RPC at this cutoff; Section 3.2 relies on
  the candidate's own repository statements and Section 3.3 on the recorded
  release artifacts.
- Patent coverage is limited to public full-text indexes; unpublished
  applications inside the 18-month window are not visible.
- Section 6 rests on one primary paper read in full and on secondary coverage
  for the round-count attribution, which is explicitly marked as unconfirmed.

## 9. Conclusion

The word "first" survives only inside the exact conjunction of §1 of the 13 July
document, and now survives with its blocking gate closed. This scan found no
public artifact at or before `2026-08-24T19:58:01Z` that combines direct
transparent proof verification, computational hiding, a real shielded-spend
statement, same-transaction nullifier and pool mutation, the 1.4M-CU cap, and a
proven Johnson/MCA 100-bit-class ledger on Solana mainnet-beta. It again found
close and important prior art for every broader subset of that sentence.
