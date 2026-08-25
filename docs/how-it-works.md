# How Aspis works

Aspis verifies a transparent private-spend proof and applies its public state
change on Solana. To our knowledge at the 24 August 2026 search cutoff, the
published transaction is the first Solana mainnet result of its exact kind:
direct trusted-setup-free proof verification followed by the corresponding
nullifier and pool update in the same atomic transaction. The private record,
owner secret, value, and Merkle path are hidden by the declared computational
hiding model.

The proof check and state update are atomic. If any instruction, account,
statement, proof, or state recheck fails, the pool and nullifier are not
changed.

## What the proof establishes

For the released one-input, one-output relation, a valid private witness
satisfies these conditions:

- it contains a record in the current pool and the secret data needed to spend
  it;
- the owner secret authorizes that record;
- the input and output use the declared asset;
- the input value equals the output value plus the public fee;
- the output commitment and next pool root are computed correctly; and
- the public nullifier is derived from the private input.

The soundness theorem classifies any accepted false statement into explicit
failure events. Lean also proves the spend-witness extraction, exact
Mersenne-field domains and encoders, coherent four-fold polynomial extraction,
the exact capped-query law, candidate and verifier-weight fold duality, theft
reductions, and the nullifier state machine. The deployed-source proof follows
any successful translated verifier call end to end through the parser,
transcript, six work checks, 18 queries, five authenticated opening sections,
four low-degree folds, 76 claims, 58 relation fields, and both final
accumulators. Its clean replay passed on 24 August 2026.

After acceptance, the program records the public nullifier and later spends
with the same marker address are rejected. Lean separately checks the
sequential marker model and reduces fixed-victim theft to eight named
cryptographic, extraction, setup, and runtime events. The
[assumptions ledger](assumptions-ledger.md) gives the exact probability and
platform interfaces used to interpret those results.

## Why the proof is uploaded first

The V5 proof is 75,358 bytes, far larger than Solana's transaction packet
limit. Aspis therefore uses a temporary program-owned proof account:

1. Create the pool and initialize it.
2. Create the proof account.
3. Upload the proof in 79 chunks of at most 960 bytes.
4. Seal the account after checking its complete byte image.
5. Verify the proof and apply the spend with the released V5 instruction.

That is 84 lifecycle transactions: 2 pool transactions, 1 proof-account
create, 79 uploads, 1 seal, and 1 spend. Program deployment and the three
post-execution cleanup transactions are separate.

Sealing prevents the proof bytes from changing between upload and
verification. During V5 verification the sealed proof is read-only and retained, so the
finalized execution can be recorded before a separate authorized close.

## The V5 verification transaction

The transaction supplies five ordered accounts:

- the sealed proof account;
- the current pool;
- the program-derived nullifier account;
- the payer; and
- the System Program.

The program then:

1. validates the instruction and every account role;
2. reconstructs the public statement from the instruction and live pool;
3. verifies the complete proof;
4. rechecks the mutable pool and nullifier state;
5. advances the pool; and
6. creates or assigns the nullifier marker.

The account-distinctness checks reject reusing one account in multiple roles.
Verification and the mutable-state recheck happen before the first write or
System Program call. Solana's writable account locks serialize spends against
one pool.

## No trusted setup

Aspis uses transparent public parameters and hash-based commitments. It has no
setup ceremony whose secret randomness must be destroyed.

The tradeoff is operational cost. The proof is large, and the prover performs
substantial proof-of-work grinding to exchange off-chain time for lower
on-chain verification cost. Aspis uses M31 arithmetic, a circle-domain
WHIR-style commitment, Poseidon2 inside the relation, and Solana's native
SHA-256 syscall for the Fiat–Shamir transcript.

The [formalization report](../paper/aspis-formalization/) defines the current
proof scope and security boundary. The earlier
[construction paper](../paper/aspis-spend/) records the protocol and
deployment design. The [assumptions ledger](assumptions-ledger.md) identifies
the cryptographic assumptions rather than treating them as Lean conclusions.

## From construction to mainnet

Aspis records four complementary evidence layers:

| Layer | Evidence |
| --- | --- |
| Mathematical construction | Lean checks the spend relation, release arithmetic, circle domains, four-fold FRI argument, distinct-query calculation, hiding reductions, theft reductions, and marker-state model |
| Selected deployed implementation | Charon and Aeneas translate the accepting Rust callback; Lean follows any successful call end to end from parsing through both final accumulators and derives the maintained security-event conclusion |
| Exact program | Pinned source and build tools reproduce the frozen SBF byte for byte |
| Chain result | Finalized receipts bind that SBF, proof, statement, state transition, compute use, and cleanup |

The [formal-verification overview](formal-verification.md) explains the exact
proof boundary. The [V5 mainnet record](v5-mainnet-demo.md) gives the chain
identities and transaction links.

## Finalized V5 result

The mainnet V5 verification transaction finalized at slot `435019536`. The transaction
used nullifier PDA bump 255. The recorded pre-execution runner source required
that value, although the immutable lifecycle evidence does not pin the exact
executed runner commit. The exact deployed program derived and checked the PDA
address but did not require that specific numeric bump. Exact signed-wire
simulation and landed metadata both reported 1,334,452 CU.

After finality:

1. The cleanup instruction closed the retained proof account and returned
   525,660,961 lamports
   to the payer.
2. ProgramData close sent 9,049,204,080 lamports directly to the pinned refund
   recipient.
3. The payer sweep sent 1,931,690,802 lamports to the same recipient and left
   the payer at zero.

The pinned recipient therefore received 10,980,894,882 lamports. The proof
refund is already included in the later payer sweep and is not added a second
time.

## Release profile

- The statement has one input and one output.
- The release has no deposit or append path, wallet, or growing privacy set;
  the demonstrated anonymity set was one.
- One pool is sequential. Separate pools increase throughput but split
  anonymity.
- Every spend leaves a persistent nullifier account.
- Proof upload and grinding are operationally expensive.
- The proved privacy view does not include fee-payer linkage, timing, network
  metadata, transaction graphs, or physical side channels.

## Earlier mainnet result

The earlier demonstration used a 65,407-byte proof and a different
proof-account lifecycle. Its often-cited count of 71 covers only one account
creation, 69 uploads, and one finalization. It excludes the two pool
transactions and the spend itself. The current release has always used the
broader 84-transaction lifecycle count.

The earlier evidence remains in the
[historical mainnet record](mainnet-demo.md). V5 is the current result.
