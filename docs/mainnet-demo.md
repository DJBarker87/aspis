# Aspis Spend mainnet demonstration

Aspis Spend executed on Solana mainnet-beta on 2026-07-16. One transaction
verified the released proof, advanced the pool sequence from 0 to 1, created
the nullifier marker, and refunded the proof account, at slot `433219840`
consuming `1,344,003` of the 1,400,000-CU cap.

```text
transaction: 3G1voggszvDMGi5PbGM1kuEMYKvh2TNMbH6hHHwndUdRQJNT7ehRFpQpksxLnx5tp2xkS5jGi359rVXk42sRPFcv
slot:        433219840
block time:  2026-07-16T06:26:33Z
CU:          1,344,003
status:      finalized, success
```

Cluster-pinned viewers:
[Solana Explorer](https://explorer.solana.com/tx/3G1voggszvDMGi5PbGM1kuEMYKvh2TNMbH6hHHwndUdRQJNT7ehRFpQpksxLnx5tp2xkS5jGi359rVXk42sRPFcv?cluster=mainnet-beta)
·
[Solscan](https://solscan.io/tx/3G1voggszvDMGi5PbGM1kuEMYKvh2TNMbH6hHHwndUdRQJNT7ehRFpQpksxLnx5tp2xkS5jGi359rVXk42sRPFcv?cluster=mainnet).

## Released instance

The transaction used the release-certified 65,407-byte proof with SHA-256
`32eb419e0c5c3ef4fa2db0d32579e88f1207547d8fb010279efeb6c05981b529`, bound to
the deployment domain
`ba43feb01d7d7f5ee3f57a6481b202066c83c6c3e76020a619c1611abbd08c8f`. The
finalized program log commits to the same proof digest under the domain
`aspis-proof-sha256-v1`. The conservative published soundness floor is
100.16 bits.

The proof is bound to the public statement, pool identity, sequence,
selector, verifier transcript, and, new in this release, the deployment
domain, so the same proof is valid only against a pool that stores the
matching domain. The mainnet program was the disposable id
`GQPNqfYF17Nj2dGsf6Q2AtiouyM67YxFZPh9LxBk2Ye3`; the pool was
`3ZRYarQZcWJQgzNwLo1Eo7PDmier3rbW41L8ccAddCvb` and the nullifier PDA
`CFJ5fYPSi4Qn6okBCZS3tXFMw7Lsz4Jy9vEAAGU5kfSU`.

## Finalized lifecycle

| Event | Finalized slot | Signature |
| --- | ---: | --- |
| SBF deployment | 433219270 | `qdeDmK712P3ifnn4hfqtEH3CzW7rssoP9hsJtCceebmAnA5qSrN34v4KE1H6tJbWbUjD7GdaZmLv2CxV823coW8` |
| Verify and apply (tag 65) | 433219840 | `3G1voggszvDMGi5PbGM1kuEMYKvh2TNMbH6hHHwndUdRQJNT7ehRFpQpksxLnx5tp2xkS5jGi359rVXk42sRPFcv` |
| Replay probe close | n/a | `51fzSDCoT53XrzoQZy69mpe2g36r4GjmBnNVj6K7F9vH7zQK9JhLyggApLjYxRbFaVigjzmq3P24myLgkagjTkd1` |
| ProgramData close | 433220251 | `3mfD5KEYXJ4ZyC2XeHW4fXKNYUqo46SA1waGeJ3CNz7fBzzxqy4rK6tiniVpx5D4ZpDziCEKgi66KUdEjyLkrVDo` |

After the spend, a sealed replay probe was simulated against the spent
nullifier and rejected with the expected nullifier error, with pool and
nullifier state unchanged. ProgramData was then closed and its
`6,434,638,320` lamports reclaimed.

## Cost and refund

The proof account's `456,402,000`-lamport rent was refunded inside the tag-65
transaction (balance equation reconciled). ProgramData rent
`6,434,638,320` was reclaimed on cleanup. The persistent on-chain state of
the release is the pool account and the nullifier marker
(`1,392,000` lamports). Transaction fees were base-rate.

## Deployment-domain binding

This release binds `deployment_domain =
sha256("aspis-spend-deployment-domain-v1" || runtime_program_id ||
domain_tag)`, stored by the pool at initialization and compared fail-closed
by the verification instruction before any proof byte is interpreted. The
mainnet domain above and the devnet rehearsal domain
`50b77813faf4df58226a1c6972952c21be88912701d881977b5eeab7ac8b6b46` are
distinct, so neither proof is valid against the
other deployment. This is verifiable from the public program id and domain
tag.
