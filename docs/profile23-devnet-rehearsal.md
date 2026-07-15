# Profile23 devnet rehearsal

Status: executed successfully on Solana devnet on 2026-07-14. The final tag65
transaction was finalized at slot `476282685`; this remains strictly devnet
rehearsal evidence and does not create a mainnet-beta claim.

The command surfaces are deliberately separate:

```text
stage2-profile23-devnet-readiness   read-only filesystem and RPC checks
stage2-profile23-devnet-execute     explicit signing/mutation surface
```

Both require explicit absolute paths for the payer, program, fresh pool and
fresh proof-account keypairs, release certificate, exact SBF, freshly mined
proof, its public-statement sidecar, Solana CLI executable, and evidence file.
Neither reads Solana CLI ambient configuration. The RPC URL, program maximum
length, and conservative fee reserve are also explicit.

The read-only form is:

```bash
NO_DNA=1 cargo run --release -p aspis-xtask -- \
  stage2-profile23-devnet-readiness \
  --rpc-url https://api.devnet.solana.com \
  --payer-keypair /secure/payer.json \
  --program-keypair /secure/program-7Q2n.json \
  --pool-keypair /secure/fresh-pool.json \
  --proof-account-keypair /secure/fresh-proof-account.json \
  --release /absolute/repo/results/stage2/profile23_one_transaction_release.json \
  --sbf /absolute/repo/target/deploy/aspis_verifier.so \
  --proof /absolute/proof/profile23-devnet.bin \
  --statement /absolute/proof/profile23-devnet.statement.json \
  --solana-cli /absolute/bin/solana \
  --evidence /absolute/evidence/profile23-devnet-finalized.json \
  --program-max-len <release-sbf-bytes> \
  --fee-reserve-lamports 100000000
```

Readiness pins the exact devnet genesis
`EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG`, a nonempty entirely green declared release
gate set with no failed gates, an exact read-only reconstruction of the complete
release report from live code (ignoring only its generation timestamp), all
release source hashes, exact proof/SBF and statement-sidecar release-instance
identities, live least-Good selector and Good23 fingerprint checks, independent
production-host verification, pairwise-distinct secure keypairs, the sidecar's
pool binding, absent fresh pool and proof accounts, the canonical nullifier
PDA's absent or supported prefunded shape, an absent or byte-exact upgradeable
program, explicit maximum length, and conservative rent plus fee funding.

Generate the pool keypair first, mine with its 32-byte public key in
`ASPIS_PROFILE23_POOL_HEX`, choose a fresh public sample-witness seed in
`ASPIS_PROFILE23_FIXTURE_SEED`, and regenerate the release certificate against
the resulting proof before running readiness. A proof or sidecar bound to the
old fixture pool, or a nullifier consumed by an earlier rehearsal, cannot pass
the pool/proof/release conjunction.

Execution repeats every check and additionally requires both:

```text
--execute-devnet
--acknowledgement I_ACKNOWLEDGE_PROFILE23_DEVNET_REHEARSAL_MUTATES_DEVNET_AND_SPENDS_DEVNET_SOL
```

It then deploys the exact SBF if the program is absent; creates and tag-63
initializes the fresh pool; creates, initializes, chunk-uploads, fully refetches
and tag-62 finalizes the proof account; verifies that upload and repeated
finalization reject afterwards; derives the canonical nullifier PDA; and
captures the exact upgradeable Program plus linked ProgramData account image
before setup. Immediately before simulating the fully signed tag65 wire, it
rechecks release SBF bytes, maximum length, upgrade authority, ProgramData
address, and byte-for-byte Program/ProgramData continuity. No other RPC call
intervenes between that recheck and simulation. The simulation uses signature
verification and no blockhash replacement, and execution submits those
identical bytes. An ambiguous submission may retry that same byte string once
and may never reconstruct a different transaction. Immediately after tag65
finality it repeats the exact deployment and continuity checks, then checks the
exact pool and nullifier images, proof-account immutability, and duplicate
rejection.

The evidence path is reserved with `create_new` and a synced
`in_progress_no_claim` marker before the first mutation. Successful completion
writes and syncs a same-directory completed file, changes it to mode `0444`,
and atomically renames it over the reservation. It records setup/final
signatures and finalized slots, transaction and
message hashes, raw account-image/data hashes, proof/SBF/release identities,
simulation and landed CU, pre/post states, and all negative teeth. It also
serializes the Program and ProgramData addresses/account hashes at the
before-setup, immediately-before-final-simulation, and after-finality
checkpoints, together with explicit exact-release and unchanged-identity
booleans. Deployment is performed by the explicit Solana CLI; its reported
final signature is refetched from devnet to derive the finalized wire and
message hashes. A future mainnet executor still needs independent handling and
evidence for any auxiliary deployment-buffer transactions hidden inside the
CLI workflow, plus the separately selected mainnet upgrade-authority policy.

## Current upload pipeline

The frozen rehearsal below used 640-byte chunks and waited for each upload to
reach finality before sending the next. Its 104 uploads spanned 3,987 slots and
24 minutes 44 seconds on the public devnet RPC.

The current executor uses 960-byte chunks. A full chunk produces a 1,173-byte
legacy transaction, leaving 59 bytes below Solana's 1,232-byte packet cap. For
the 64,447-byte release proof this gives 68 uploads, submitted in windows of
16 with batched status polling for each window. The resulting upload
schedule has five finality waves: 16, 16, 16, 16, and 4 transactions.

Every transaction in a window uses the same fresh blockhash but has a distinct
signed message. The executor retains that exact wire and may rebroadcast the
same signature up to three times when it remains unseen; it never re-signs.
It preserves the transaction ledger in chunk order, aborts on expiry or any
landed error, and does not submit tag 62 until every upload is finalized and a
finalized RPC read matches the complete expected account image. The recorded
public-RPC timings project an upload phase of roughly 80--120 seconds.

## Finalized q18/g37 rehearsal

The released 64,447-byte proof and 921,848-byte SBF were exercised against
program `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`. The fresh proof
account used 68 uploads and the recorded setup lifecycle contained 73
transactions. The executor validated the exact finalized account state before
submitting tag65.

The final transaction is:

```text
signature: 4HRnTBPqSh9HW4Nw52rJgnd36fzR6CiKgiaL29WkeH4Gk4xLJVhGEt9CAStyUTpuajo9sw4iDLXQHWwFFQALWmto
slot:      476282685
CU:        1340749 simulated, 1340749 landed
retry:     none
```

It advanced the pool sequence from 0 to 1, created the canonical nullifier
marker, preserved the sealed proof-account image, and left duplicate
simulation rejected. Post-finalization upload and second-finalization
simulations also rejected. The Program and linked ProgramData account images
were unchanged between the immediately-before-simulation and after-finality
checkpoints. The program remained upgradeable under the recorded rehearsal
authority.

The completed mode-`0444` evidence file is 48,131 bytes and has SHA-256:

```text
e761782d6067a667bd36fff24322d199400382e2b869aa78a54e92b18ce3f440
```

The public transaction can be inspected at
`https://explorer.solana.com/tx/4HRnTBPqSh9HW4Nw52rJgnd36fzR6CiKgiaL29WkeH4Gk4xLJVhGEt9CAStyUTpuajo9sw4iDLXQHWwFFQALWmto?cluster=devnet`.
