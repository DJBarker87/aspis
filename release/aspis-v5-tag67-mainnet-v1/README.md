# Aspis V5 Tag-67 mainnet record

This directory is the sanitized public record for the finalized Aspis V5
mainnet-beta demonstration on 25 July 2026 in Europe/Berlin (24 July UTC). It
supplements, and does not mutate, the frozen candidate in
`release/aspis-v5-tag67-frozen-candidate-v1/`.

The release records four linked facts:

1. the maintained Lean project checks substantial parts of the mathematical
   construction;
2. Charon/Aeneas translations and Lean bridge proofs connect selected
   production Rust to those models for the stated release scope;
3. the pinned source and build tools reproduce the exact compiled Solana
   program; and
4. that program completed the finalized mainnet transaction below.

`formal/formal-evidence.json` preserves the formal record made at release time
and adds the 14 August 2026 review. The newer Lean proofs show that a suitably
extracted verifier trace satisfies the complete spend relation, and reduce two
ways of spending someone else's record to named extraction or hash-security
failures. They do not yet prove that every accepted deployed Tag-67 execution
produces that trace, or give one numerical theft-probability bound for the
deployed system. The file lists those and the other remaining proof gaps
explicitly.

The final Tag-67 transaction is
[`EJvi…J2fE`](https://explorer.solana.com/tx/EJviPgF12i9iK2CveVaQSMeFQqDMFPQ1iPRUYEwNQE3zGquTUZNJXPZEENorcQtsnQj1orFmH1TPsgdbR3vJ2fE).
It finalized at slot `435019536`, consumed `1,334,452` CU in both exact
simulation and landing, and used nullifier PDA bump `255`.

The cleanup then finalized in this order:

1. Tag 64 closed the retained proof account and returned `525,660,961`
   lamports to the payer.
2. Loader-v3 ProgramData close sent `9,049,204,080` lamports directly to the
   locally pinned refund wallet.
3. The payer sweep sent `1,931,690,802` lamports to the same wallet and left
   the payer at zero.

The pinned wallet therefore received `10,980,894,882` lamports
(`10.980894882 SOL`) from the two direct refund transactions. The program,
pool, and nullifier accounts retain `3,981,120` lamports in total.

## Contents

- `evidence/mainnet-lifecycle.json` — sanitized receipts and reconciliation.
- `proof/v5-mainnet-proof.bin` — exact proof verified by Tag 67.
- `statement/v5-mainnet-statement.json` — exact public statement.
- `formal/formal-evidence.json` — release-specific formal coverage, source
  identities, assumptions boundary, and replay entry points.
- `manifest.json` and `SHA256SUMS` — bundle identities.
- `verify.sh` — offline file and invariant checks.

The exact frozen SBF is referenced from the immutable candidate bundle by
path and SHA-256. No RPC key, keypair, signed-wire spool, or private local
path is included here.

## Transaction count

V5 used `84` core lifecycle transactions:

- 2 pool setup transactions;
- 1 proof-account create;
- 79 proof uploads;
- 1 Tag-62 proof finalization;
- 1 Tag-67 spend.

Deployment and cleanup are separate. The older q18 proof setup count of `71`
was `1 create + 69 uploads + 1 finalize`; the executor never switched from 71
to 84 during this run.

Run `./verify.sh` from this directory to check the bundle without network
access.
