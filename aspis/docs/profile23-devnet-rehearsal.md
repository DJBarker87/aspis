# Profile23 devnet rehearsal

Status: executed successfully on Solana devnet on 2026-07-14. The final tag-60
transaction was finalized at slot `476231605`; this remains strictly devnet
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
`ASPIS_PROFILE23_POOL_HEX`, and regenerate the release certificate against the
resulting proof before running readiness. A proof or sidecar bound to the old
fixture pool cannot pass the pool/proof/release conjunction.

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
before setup. Immediately before simulating the fully signed tag-60 wire, it
rechecks release SBF bytes, maximum length, upgrade authority, ProgramData
address, and byte-for-byte Program/ProgramData continuity. No other RPC call
intervenes between that recheck and simulation. The simulation uses signature
verification and no blockhash replacement, and execution submits those
identical bytes. An ambiguous submission may retry that same byte string once
and may never reconstruct a different transaction. Immediately after tag-60
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

## Finalized q18/g37 rehearsal

The released 66,367-byte proof and 915,656-byte SBF were exercised against
program `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`. The fresh proof
account used 104 uploads and the complete prerequisite lifecycle contained
109 setup transactions. The successful invocation resumed from an explicit
checkpoint only after the executor reconstructed three finalized signed
transactions and validated the exact account state; recovered transactions
were not resent.

The final transaction is:

```text
signature: 3ofPbzRkqMEJZCM9vwKz96rLqRFtSg4d1GyqqVBEbogtwzmJodsWb2f7V4X83BLvuPXFsT6Yyf87PC1ZbLf1R7bx
slot:      476231605
CU:        1314332 simulated, 1314332 landed
retry:     none
```

It advanced the pool sequence from 0 to 1, created the canonical nullifier
marker, preserved the sealed proof-account image, and left duplicate
simulation rejected. Post-finalization upload and second-finalization
simulations also rejected. The Program and linked ProgramData account images
were unchanged between the immediately-before-simulation and after-finality
checkpoints. The program remained upgradeable under the recorded rehearsal
authority.

The completed mode-`0444` evidence file is 61,342 bytes and has SHA-256:

```text
360e38fc5db3b644586c29e7a872203e8f9507c9ddef52add776fefb5d300275
```

The public transaction can be inspected at
`https://explorer.solana.com/tx/3ofPbzRkqMEJZCM9vwKz96rLqRFtSg4d1GyqqVBEbogtwzmJodsWb2f7V4X83BLvuPXFsT6Yyf87PC1ZbLf1R7bx?cluster=devnet`.
