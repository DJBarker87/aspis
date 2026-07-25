# V5 mainnet result

On 25 July 2026 in Europe/Berlin (24 July UTC), the current Aspis release
completed its private-spend verification and state update on Solana
mainnet-beta. In one transaction, the program:

- checked the complete 75,358-byte proof;
- advanced the pool from sequence zero to sequence one; and
- created the one-time spent marker that prevents reuse of the private record.

The transaction consumed 1,334,452 of Solana's 1,400,000-unit transaction
limit. It finalized successfully at slot `435019536`:
[`EJviPgF…R3vJ2fE`](https://explorer.solana.com/tx/EJviPgF12i9iK2CveVaQSMeFQqDMFPQ1iPRUYEwNQE3zGquTUZNJXPZEENorcQtsnQj1orFmH1TPsgdbR3vJ2fE?cluster=mainnet-beta).

## The evidence behind the transaction

The transaction is the observed final stage of a longer evidence chain:

| Layer | What is recorded |
| --- | --- |
| Mathematical model | Lean checks substantial parts of the construction, release calculations, and maintained V5 verifier model |
| Selected production Rust | Charon/Aeneas translations and Lean bridge proofs connect the selected release path to those models |
| Compiled program | Pinned source and build tools reproduce the exact Solana program byte for byte |
| Mainnet execution | Program identity, exact proof, finalized state transition, compute use, and account changes are recorded below |

The accessible coverage explanation is
[What has been formally checked](formal-verification.md). The release-specific
toolchain, theorem, source hashes, replay commands, and remaining
transcript-hash-call equality are bound in
[`formal-evidence.json`](../release/aspis-v5-tag67-mainnet-v1/formal/formal-evidence.json).

## Exact technical record

| Item | Value |
| --- | --- |
| Program | `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue` |
| Pool | `u99qswA5FJbaMdJN23XEBUiyKmiyBcRidWHrzUz8VTm` |
| Uploaded proof account | `3cb9NKGgNayZfTnGzNkWiwbHfQZyaonMFRxvAF8dEfUM` |
| Nullifier account | `7Umhkv2Z3E2DksnpivCz2tovtbRoL1uXtnYBAtQBgu8Q` |
| Nullifier PDA bump | `255` |
| SBF SHA-256 | `4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40` |
| Proof SHA-256 | `330414df587974684643a6062d092db0519d746f0c7efe4ed2108775b685feaf` |
| Statement SHA-256 | `0cdc34bc7f835640cff76d1085df9ba966df9f39eb228f3002f927cf30958113` |

The frozen SBF was deployed in
[`RHt7eEr…Ndp3RMf`](https://explorer.solana.com/tx/RHt7eErpgLvc7Z2QDWVSj4dmYTg9s4bU62CgWfN5Y1N2BUkAMmQ1V3P8RhtpX9px7aUfAYa8CNSo5Rx5Ndp3RMf?cluster=mainnet-beta)
at slot `434999519`. The finalized state transition is
[`EJviPgF…R3vJ2fE`](https://explorer.solana.com/tx/EJviPgF12i9iK2CveVaQSMeFQqDMFPQ1iPRUYEwNQE3zGquTUZNJXPZEENorcQtsnQj1orFmH1TPsgdbR3vJ2fE?cluster=mainnet-beta).

The exact signed wire simulated at 1,334,452 CU and landed at exactly
1,334,452 CU. The canonical nullifier PDA bump was 255. These are deployment
and replay facts in the technical record, not prerequisites for understanding
the result.

## Transaction count

The V5 spend lifecycle comprised 84 transactions:

| Phase | Transactions |
| --- | ---: |
| Pool create and initialize | 2 |
| Proof-account create | 1 |
| Proof uploads, up to 960 bytes per chunk | 79 |
| Tag-62 proof seal | 1 |
| Tag-67 verify and apply | 1 |
| **Total** | **84** |

This did not change from 71 to 84 during the run. The q18/g37 figure of 71
counts only its proof-account setup: one create, 69 uploads, and one finalize.
It excludes that release's two pool transactions and final Tag-65 spend. V5's
proof is larger, so it required ten more upload chunks, and the V5 total also
uses the broader end-to-end lifecycle count. Program deployment and the three
post-execution cleanup transactions are separate.

The resumed Tag-67 lifecycle finalized every write it submitted. Earlier
unsuccessful Tag-67 candidate-wire attempts did not produce failed on-chain
spend transactions. The successful deployment and cleanup transactions are
accounted separately.

## Cleanup and refund

After Tag 67 was finalized and recorded, cleanup proceeded in three finalized
transactions:

| Action | Finalized transaction | Slot | CU | Fee | Value moved |
| --- | --- | ---: | ---: | ---: | ---: |
| Close retained proof account | [`5FF19Ec…71hZXbW`](https://explorer.solana.com/tx/5FF19EceNFBVbrNzvhxTnbK8bWSysAHVLRjbfggamY3YSeUFzdk54c4GT9GKitBWGkntNG2Zx9xHgbzp371hZXbW?cluster=mainnet-beta) | `435019649` | 781 | 10,000 lamports | 525,660,961 lamports to the payer |
| Close ProgramData | [`uZ6q5a2…kBdHkWn`](https://explorer.solana.com/tx/uZ6q5a2jGYcscEZgnLghPrqNwp9Hxq3REgYmt6gnb3JuorkUUEQUeJkVWy2e88j9bSLHgRvT2DytjRW2kBdHkWn?cluster=mainnet-beta) | `435019804` | 2,520 | 10,000 lamports | 9,049,204,080 lamports directly to the pinned recipient |
| Sweep payer | [`4haJ6dP…zbj1JyUW`](https://explorer.solana.com/tx/4haJ6dPmSFkscFKC57QoCUUcf46vU77av9Y8UfcRyCWjfydzHjCeJCsfuthmifXJfVWreZZM8JTDUdBgzbj1JyUW?cluster=mainnet-beta) | `435020068` | 150 | 5,000 lamports | 1,931,690,802 lamports to the pinned recipient |

The locally pinned refund recipient was
`Dni6HwfsjJ3sQFTEtKVGL6RgE7zAXnKA7K8MLBBm2RZp`. It received
9,049,204,080 + 1,931,690,802 = **10,980,894,882 lamports**
(10.980894882 SOL). The proof-account rent first returned to the payer and is
therefore already included in the later payer sweep; it must not be added to
the recipient total a second time. The payer's finalized post-sweep balance
was zero.

The cleanup path pins the refund address independently of mutable account
balances. The ProgramData refund went directly to that address. The final
sweep signed an exact payer-balance snapshot minus its transaction fee, so
unrelated inbound lamports could not redirect the refund.

The earlier q18/g37 demonstration and its different lifecycle are preserved
unchanged in [the q18/g37 mainnet record](mainnet-demo.md). Machine-readable
release identities and measurements are in
[`release/release-facts.json`](../release/release-facts.json). The sanitized
proof, statement, finalized lifecycle receipts, and reconciliation are in the
offline-verifiable
[`release/aspis-v5-tag67-mainnet-v1/`](../release/aspis-v5-tag67-mainnet-v1/)
bundle; run its
[`verify.sh`](../release/aspis-v5-tag67-mainnet-v1/verify.sh) from the
repository checkout.
