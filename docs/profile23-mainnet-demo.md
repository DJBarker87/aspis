# Profile23 mainnet demonstration

Profile23 was executed successfully on Solana mainnet-beta on 2026-07-14. The
single verification-and-state-transition transaction finalized at slot
`432933949`, consumed `1,343,749` compute units, advanced the pool sequence
from 0 to 1, created the nullifier marker, and refunded the proof account's
`449,720,400` lamports.

```text
transaction: 4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo
slot:        432933949
block time:  2026-07-14T21:40:36Z
CU:          1,343,749
status:      finalized, success
```

Use a cluster-pinned viewer: [Solana Explorer](https://explorer.solana.com/tx/4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo?cluster=mainnet-beta)
or [Solscan](https://solscan.io/tx/4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo?cluster=mainnet).

## Exact released instance

The transaction used the release-certified 64,447-byte proof with SHA-256
`d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d` and
the 921,848-byte SBF image with SHA-256
`97c45a9abef97607a2fc6ed245829210046b234044b6738599d2bce0c367d04a`.
The finalized program log commits to the same proof digest under the domain
`aspis-proof-sha256-v1`. The conservative published soundness floor is
`100.16144938287457` bits.

A new proof grind was not needed for mainnet. The proof is bound to the exact
public statement, pool identity, sequence, selector, and verifier transcript;
the Solana cluster is not an input to that relation. Mainnet therefore reused
the exact release-certified proof while deploying the exact release-certified
SBF under a fresh disposable mainnet program ID. The live executor required
the certified pool and nullifier addresses to be absent before setup.

The disposable program was
`9kPpUknrRicMvaGa6zPNERGUYDj6fMvMR8PwMS3iFR6Z`, the pool was
`B1z4gQ82xerghDKZ68HuP2Tehx5ER5mfVHq74y4ew3kk`, and the canonical nullifier
PDA was `2CnUJycxkinN3XtpWH5bCYVDEuMx42BTnFU9WXsymAu3`.

## Finalized lifecycle

| Event | Finalized slot | Signature |
|---|---:|---|
| Exact SBF deployment | 432933454 | `3BFmYhQtjWioSLRxUoV1mVCvuaBTLy5cS2S3Gi8LjXz3rFJ1u8t2Lu31kbNYSHTy9VhfrUksEUbs9esZY2PJdd4Q` |
| Tag 65 verify and apply | 432933949 | `4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo` |
| Replay probe close | 432934056 | `5NEPT1TD34p7fN1yKTCEDH1cBwY1HLgJFH4Y1yMD8GkLP9gGYGPjKgQaapsnMwRNpr1BVTopGYsHgEEpKEVwiurN` |
| ProgramData close | 432934227 | `3ZsVsjAP4wtA6KM6PygR272Wy1tuxMR9c4Zy4A4YAnTNekuTpQeUCXa8DKnpyEY52bRL8HUjz5AcQpBk4Pw9vwNk` |
| Refund sweep | 432934316 | `2o49MBB2GHRe3ECrDpnrUpmk3DwpfsFHJ7AuTJXp1BcV9EJMGdYFUEeQrxi7yYiehreP8RUa8tiKZQUNAigjwygZ` |

After the successful spend, a sealed replay probe was simulated against the
spent nullifier and rejected with the exact expected nullifier error. Its state
and the pool/nullifier state remained unchanged, after which its full
`1,176,240`-lamport rent was refunded. ProgramData was then closed and its
full `6,417,266,160` lamports were reclaimed.

## Cost and refund

| Quantity | Lamports | SOL |
|---|---:|---:|
| Initial demo payer balance | 7,000,021,000 | 7.000021000 |
| Returned to the funding source | 6,985,137,600 | 6.985137600 |
| Retained Program, pool, and nullifier rent | 3,758,400 | 0.003758400 |
| All payer-paid transaction fees | 11,125,000 | 0.011125000 |
| Exact demo-payer nonrefundable cost | 14,883,400 | 0.014883400 |
| Final demo payer balance | 0 | 0 |

The exact reconciliation is

```text
7,000,021,000 - 6,985,137,600 = 14,883,400
1,141,440 + 1,224,960 + 1,392,000 = 3,758,400
14,883,400 - 3,758,400 = 11,125,000
```

At the pinned pre-execution quote of USD 77.26 per SOL, the final cost was
USD 1.149891484. At the policy's 10% safety-adjusted price of USD 84.986, it
was USD 1.2648806324, below the USD 20 hard cap.

This reconciliation is the demo payer's balance depletion. It excludes the
inbound funding transaction fee, which was paid separately by the funding
source.

## Independent verification

The official Solana mainnet RPC and an independent PublicNode mainnet RPC
returned the same genesis hash, first transaction signatures, slots, block
times, transaction metadata, verification program log, and final account
images for the funding, deployment, verification, replay-close, ProgramData
cleanup, and sweep records. Both report the demo payer and ProgramData account
absent after cleanup. Querying the verification signature on the official
devnet and testnet RPCs returned `null`.

The publication-grade record is
[profile23_mainnet_finalized_manifest.json](../results/stage2/profile23_mainnet_finalized_manifest.json).
The sanitized provider observations are
[profile23_mainnet_independent_rpc_reconciliation.json](../results/stage2/profile23_mainnet_independent_rpc_reconciliation.json).
Neither file contains local keypair paths or key material.
