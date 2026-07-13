# Profile23 devnet rehearsal

Status: implemented and compile-tested, but not executed. This workflow is
strictly devnet rehearsal evidence; it cannot create a mainnet-beta claim.

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
`EtWTRABZaYq6iMfeYKouRu166VU2xqa1`, exactly 30 green release gates and all
release source hashes, proof/SBF identity, pairwise-distinct secure keypairs,
the sidecar's pool binding and canonical public fields, absent fresh pool and
proof accounts, the canonical nullifier PDA's absent or supported prefunded
shape, an absent or byte-exact upgradeable program, explicit maximum length,
and conservative rent plus fee funding.

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
finalization reject afterwards; derives the canonical nullifier PDA; simulates
one fully signed tag-60 wire with signature verification and no blockhash
replacement; and submits those identical bytes. An ambiguous submission may
retry that same byte string once and may never reconstruct a different
transaction. After finality it checks the exact pool and nullifier images,
proof-account immutability, and duplicate rejection.

The evidence path is reserved with `create_new` and a synced
`in_progress_no_claim` marker before the first mutation. Successful completion
writes and syncs a same-directory completed file, changes it to mode `0444`,
and atomically renames it over the reservation. It records setup/final
signatures and finalized slots, transaction and
message hashes, raw account-image/data hashes, proof/SBF/release identities,
simulation and landed CU, pre/post states, and all negative teeth. Deployment
is performed by the explicit Solana CLI; its reported final signature is
refetched from devnet to derive the finalized wire and message hashes. A
future mainnet executor still needs independent handling and evidence for any
auxiliary deployment-buffer transactions hidden inside the CLI workflow, plus
the separately selected mainnet upgrade-authority policy.
