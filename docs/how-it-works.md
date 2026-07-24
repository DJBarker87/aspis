# How Aspis works

Aspis checks a private spend and applies its state change entirely on Solana.
The person spending proves that a private record satisfies the pool's rules
without publishing the record, its owner secret, its value, or its Merkle path.

The proof and the state update are one all-or-nothing operation. If any check
fails, the pool and spent-marker accounts remain unchanged.

## What the proof establishes

For the released one-input, one-output construction, the proof establishes
that:

- the spender knows a record in the current pool;
- the owner secret authorizes that record;
- the input and output use the declared asset;
- the input value equals the output value plus the public fee;
- the output commitment and next pool root are computed correctly; and
- the one-time spent marker is derived from the private input.

The spent marker is public. It prevents the same private record from being used
twice without revealing which record was spent.

## Why the proof is uploaded first

The proof is much larger than a Solana transaction packet. Aspis therefore
stores it in a temporary program-owned account:

1. The prover creates the proof account.
2. The proof is uploaded in chunks.
3. The program seals the account after checking its complete byte image.
4. The spend transaction verifies the sealed proof in place.
5. The q18/g37 release closed the temporary proof account in the spend.
   V5 retains it as evidence until a separate close transaction returns its
   rent to the operator.

Sealing prevents the proof from changing between upload and verification.

## The spend transaction

The spend transaction supplies the sealed proof account, current pool account,
canonical spent-marker account, payer, and System Program.

The program then:

1. checks the instruction bytes and all account roles;
2. reconstructs the public statement from the instruction and live pool state;
3. verifies the complete proof;
4. rechecks the mutable state;
5. advances the pool;
6. creates or assigns the canonical spent-marker account.

The q18/g37 path also closed and refunded the proof account in this
transaction. V5 keeps the proof account unchanged during the spend and closes
it separately after the result has been recorded.

Solana account locking serializes writes to one pool. The program performs no
state change unless every verification and account check succeeds.

## No trusted setup

Aspis uses public parameters and hash-based commitments. It does not rely on a
setup ceremony with secret randomness that must be destroyed.

The tradeoff is proof size and compute. Aspis uses a pre-uploaded proof account,
Solana's native SHA-256 syscall, high-rate expansion, a small number of
verifier queries, and proof-of-work grinding to fit the complete check within
one transaction.

## From mathematics to the program

The repository records four distinct forms of evidence:

1. Lean checks substantial parts of the private-spend mathematics and release
   calculations.
2. Charon and Aeneas translate selected production Rust into Lean, where
   bridge proofs connect it to the mathematical models.
3. The pinned build-source commit and tools reproduce the compiled Solana
   program byte for byte.
4. Finalized transactions and account records show what the program executed.

The exact formal scope is explained in
[How Aspis is formally checked](formal-verification.md).

## Current results

The q18/g37 release completed a finalized mainnet transaction on 2026-07-16 at
1,344,003 CU.

V5 Tag 67 is the current candidate. Its frozen program completed the full state
transition on devnet at 1,335,952 CU and has been replayed on the current
mainnet runtime. Its mainnet transaction is pending.

See the [main README](../README.md) for current release identities and the
[paper](../paper/aspis-spend/) for the complete construction.

## Scope

The current construction demonstrates one input, one output, and one
sequential pool. It does not yet provide deposits, multiple inputs or outputs,
a wallet, or a growing privacy set.
