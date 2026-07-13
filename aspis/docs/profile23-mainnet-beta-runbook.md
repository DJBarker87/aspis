# Profile23 mainnet-beta execution runbook

Status: execution design only. The repository currently has a fail-closed,
read-only readiness command. It has no code path that signs, deploys, creates an
account, uploads a proof, or submits a transaction. A mainnet signature must
not be claimed until the live executor below has been implemented, reviewed,
run, finalized, and independently checked.

## Claim boundary

The eventual one-transaction claim is exactly one finalized tag-60
transaction that both verifies a finalized Profile23 proof account and commits
the pool transition plus nullifier marker. Program deployment, pool-account
creation and initialization, proof-account creation, proof uploads, and
`FinalizeProof` are prior setup transactions. They are not included in the
one-transaction claim and must remain adjacent to it whenever the result is
reported.

The declared program id is
`7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`. The deployment keypair's
public key must match it exactly. Neither this note nor any generated artifact
may contain secret key bytes, RPC credentials, or an unredacted credentialed
RPC URL.

The frozen local release input is 30/30 gates green: the 61,599-byte proof has
SHA-256
`35c4e79316bf4a2af1951e5d2f41b6ebb4ebb7bd1e91a3ba93c52e549bfe7949`,
and the 6,870,048-byte default SBF has SHA-256
`6b64baf559dcddbd6f9b1af1205effeb6afae6a5746a44421e8826251fe4cffb`.
Production proof accounts are sealed with append-only tag 62; append-only tag
63 initializes the live pool. These local facts are prerequisites, not
mainnet evidence.

## Read-only readiness

Set these variables in the invoking shell or secret manager; do not commit
them:

```text
ASPIS_PROFILE23_MAINNET_RPC_URL=https://<dedicated-paid-provider>/<credential>
ASPIS_PROFILE23_MAINNET_RPC_IS_PRIVATE=I_CONFIRM_THIS_IS_A_DEDICATED_PAID_MAINNET_RPC
ASPIS_PROFILE23_MAINNET_AUDIT_RPC_URL=https://<different-provider>/<different-credential>
ASPIS_PROFILE23_MAINNET_AUDIT_RPC_IS_INDEPENDENT=I_CONFIRM_THIS_IS_A_DISTINCT_MAINNET_RPC_PROVIDER
ASPIS_PROFILE23_MAINNET_PAYER_KEYPAIR=/secure/path/payer.json
ASPIS_PROFILE23_MAINNET_PROGRAM_KEYPAIR=/secure/path/7Q2n...json
ASPIS_PROFILE23_UPGRADE_POLICY=immutable
```

The audit RPC variables are reserved for the future live executor and
independent checker; the current read-only readiness command does not consume
or validate them. The audit endpoint must use a different provider hostname
and different credentials, not merely a second URL at the primary provider.

For a deliberately retained keypair authority, use
`ASPIS_PROFILE23_UPGRADE_POLICY=keypair`, set
`ASPIS_PROFILE23_MAINNET_UPGRADE_AUTHORITY_KEYPAIR`, and set
`ASPIS_PROFILE23_ACCEPT_SINGLE_KEY_UPGRADE_RISK` to the exact acknowledgement
required by the command. Immutable is the release default. A multisig/governed
authority needs a separately reviewed implementation; it must not be smuggled
through the single-key path.

Run:

```bash
NO_DNA=1 cargo run --release -p aspis-xtask -- \
  stage2-profile23-mainnet-readiness
```

The command writes
`results/stage2/profile23_mainnet_beta_readiness.json` even when it fails. It
requires all of the following:

1. the exact current Profile23 release certificate declares release and every
   embedded release gate is green;
2. every file pinned by that certificate still has the pinned size and
   SHA-256;
3. the local proof and SBF exactly match the certificate;
4. the RPC is HTTPS, is neither local nor a known public endpoint, and carries
   an explicit dedicated/private-provider acknowledgement;
5. `getGenesisHash` is exactly mainnet-beta's genesis hash;
6. payer and deployment keypair files are regular non-symlink files with no
   group/other permission bits, and the deployment pubkey equals the declared
   id;
7. an existing program is a valid upgradeable-loader program whose deployed
   bytes exactly equal the release SBF (allowing only zero program-data
   padding), or the declared address is absent and ready for a fresh deploy;
8. the observed upgrade authority matches the selected policy; and
9. the payer covers a conservative peak budget: buffer rent, ProgramData rent,
   program-account rent, pool rent, proof-account rent, nullifier-marker rent,
   and an explicit fee reserve. Buffer rent is counted even though a successful
   deployment normally reclaims it.

The final `reviewed_live_executor_available` gate is intentionally red until a
separate live executor is implemented and reviewed. Passing all local/network
prerequisites is not a mainnet deployment and produces no signature.

`--execute` is deliberately rejected. It cannot opt this read-only command into
mutating behavior.

## Live executor that remains to be implemented

The executor must be a separate command with two simultaneous interlocks:

- an explicit `--execute-mainnet-beta` flag; and
- an exact, long-form environment acknowledgement that the operation spends
  real SOL and mutates mainnet-beta.

It must repeat every readiness check after parsing the interlocks and
immediately before its first signature. A cached readiness JSON is evidence,
not authority to proceed. It must never read endpoint, payer, program-id, or
upgrade-authority defaults from the ambient Solana CLI configuration.

### Phase 0: freeze the real statement and release before mutation

This phase happens before program deployment, pool creation, or any other
mainnet write.

1. Generate the real pool keypair offline, persist it in a protected recovery
   location, and record only its pubkey in artifacts. Select the initial
   sequence (normally zero), canonical initial anchor, and matching private
   witness. Generate the proof-account keypair now or during setup; its secret
   bytes likewise never enter logs or artifacts.
2. Mine a fresh Profile23 proof with
   `ASPIS_PROFILE23_POOL_HEX=<real pool pubkey bytes>` and the exact selected
   sequence and anchor. Require the independently generated sidecar to bind the
   same pool pubkey, sequence, current anchor, nullifier, output commitment,
   output anchor, asset id, and fee. A proof for the old `[0x5a; 32]` fixture is
   ineligible.
3. Run the complete release suite against that exact proof and exact production
   SBF:

   ```bash
   NO_DNA=1 cargo run --release -p aspis-xtask -- \
     stage2-profile23-one-transaction-release
   ```

   Require the release certificate to declare release and every embedded gate
   green. Freeze the release-certificate, proof, sidecar, and SBF sizes and
   SHA-256 values. Re-run read-only readiness against those frozen objects.
4. Freeze the exact final transaction-envelope policy too: version, fee payer,
   1,400,000-CU limit, 262,144-byte heap request, priority-fee choice, verifier
   instruction bytes, and account order. Any later change requires a new
   release certificate and restarts Phase 0. The future release gate must
   compare this manifest with the envelope used by its measured transaction;
   the current fixture certificate does not authorize an unmeasured envelope.

No mainnet transaction may be signed unless Phase 0 is green. This ordering
prevents an initialized real pool or paid proof account from becoming the
input to a proof/release run that later fails.

### Phase 1: deploy and pin the program

Rebuild nothing. Load only the release-pinned SBF. For a fresh deployment the
executor must construct the equivalent of the following argument manifest,
with the full URL and keypair paths supplied directly:

```text
solana program deploy
  --url <ASPIS_PROFILE23_MAINNET_RPC_URL>
  --use-rpc
  --keypair <ASPIS_PROFILE23_MAINNET_PAYER_KEYPAIR>
  --program-id <ASPIS_PROFILE23_MAINNET_PROGRAM_KEYPAIR>
  --fee-payer <ASPIS_PROFILE23_MAINNET_PAYER_KEYPAIR>
  --upgrade-authority <exact selected authority keypair>
  --commitment finalized
  --max-len 6870048
  --max-sign-attempts 1
  --output json
  [--final when ASPIS_PROFILE23_UPGRADE_POLICY=immutable]
  <exact release-pinned SBF path>
```

`--max-len` must equal the selected release certificate's
`default_production_sbf.bytes` (currently 6,870,048), not an ambient or CLI
default. `--skip-preflight` and `--skip-feature-verify` are forbidden. Record
every buffer/deploy signature and finalized slot. The one-attempt setting makes
CLI resigning visible; a failed or ambiguous setup step is reconciled by
account address and known signature before a controlled retry.

If the program already exists, do not redeploy merely for ceremony. Refetch
the finalized Program and ProgramData accounts, decode the upgradeable-loader
link, and require the deployed code length and bytes to equal the SBF exactly;
all remaining ProgramData capacity must be zero. Record the ProgramData
address, maximum capacity, complete raw-account SHA-256, deployed-code SHA-256,
and authority.

For `immutable`, prefer `--final` during a fresh deployment. If an already
deployed exact binary still has an authority, the separate finalization command
must explicitly pass `--url`, `--keypair`, `--fee-payer`,
`--upgrade-authority`, `--commitment finalized`, `--output json`, and `--final`;
`--skip-preflight` remains forbidden. Record its signature and finalized slot,
then refetch ProgramData and require authority `None`. For a retained keypair
authority, require exact pubkey equality and emit a prominent risk field.
Immutability is irreversible and must be selected only after the complete
release and deployment rehearsal are reviewed.

Do not proceed if any program byte, owner, executable flag, loader link,
capacity byte, or authority differs.

### Phase 2: create and seal the frozen setup accounts

1. Create the already selected pool account with exact
   `ATOMIC_POOL_STATE_LEN`, rent exemption, and verifier-program ownership.
2. Invoke append-only tag 63 (`InitializeAtomicPool`) with the pool account
   writable and signing, using the already frozen sequence and anchor. Refetch
   at finalized commitment and require the exact encoded state.
3. Create the proof account with exact
   `PROOF_ACCOUNT_HEADER_LEN + proof_bytes`, rent exemption, and
   verifier-program ownership.
4. Call `InitProof`, upload every chunk, and read the complete account back.
   Require the header, declared length, payload bytes, and payload SHA-256 to
   match the frozen proof. Only then call append-only tag 62
   (`FinalizeProof`). Refetch at finalized commitment and require the authority
   bytes to be all zero and every payload byte unchanged.

Every setup signature, purpose, and finalized slot belongs in the evidence's
`setup_transactions` array. These transactions do not count as the claimed
atomic verification/state transaction. Setup retries must reconcile the known
signature and exact target account first: repeat uploads may write the same
bytes, but conflicting bytes, a different account, or a different frozen
statement are fatal.

### Phase 3: coherent snapshot and nullifier prestate

1. Decode the frozen proof and sidecar again. Require the pool pubkey,
   sequence, current anchor, nullifier, output commitment, output anchor, asset
   id, and fee to match the finalized pool and Phase-0 manifest.
2. Derive the nullifier address using the program's exported
   `atomic_nullifier_address(program_id, nullifier)`. Its seeds are exactly
   `b"aspis-nullifier-v1"` and the 32-byte nullifier, under the verifier program
   id. The pool pubkey is stored in the marker but is **not** a PDA seed.
3. Fetch Program, ProgramData, proof, pool, nullifier PDA, payer, and System
   Program in a coherent finalized snapshot. Use `getMultipleAccounts` where
   possible, record its `context.slot`, and pass that slot as `minContextSlot`
   on all later primary-provider reads, blockhash requests, and simulations.
   Separate readiness reads do not satisfy this requirement.
4. Record the nullifier PDA's raw prestate owner, lamports, data length, and
   SHA-256, and classify it as exactly one accepted form:

   - absent/zero-lamport system-owned empty data: the program uses
     `create_account`;
   - prefunded system-owned empty data: the program transfers any rent deficit,
     then uses `allocate` and `assign`; or
   - program-owned, exactly `ATOMIC_NULLIFIER_MARKER_LEN` (72) zero bytes: the
     preallocated marker path uses no System Program creation CPI.

   A correctly initialized marker for this nullifier is a duplicate spend and
   must abort before submission. Any other owner, length, nonzero program-owned
   bytes, or malformed marker is invalid. The executor must never require
   absence: anyone can prefund the canonical PDA, and absence-only handling
   would permit public griefing.

The release review and live simulation must cover the accepted prestate path
actually observed. Because a third party can prefund the PDA after simulation,
the release suite must also measure both prefunded-system variants (with and
without a rent-deficit transfer) below the CU cap. The current certificate's
canonical-create and program-owned-zeroed measurements do not, by themselves,
price those variants; adding that release gate is a pre-mainnet blocker. The
final evidence must record the inner System Program CPI path actually executed.

### Phase 4: sign and simulate one exact candidate

1. Obtain a fresh finalized blockhash and `lastValidBlockHeight` at or after the
   coherent snapshot's context slot.
2. Construct exactly one candidate with the frozen transaction version, fee
   payer, compute-unit price, and top-level instructions in frozen order:

   - `set_compute_unit_limit(1_400_000)`;
   - `request_heap_frame(262_144)`;
   - the frozen compute-unit-price instruction if the selected price is
     nonzero; and
   - exactly one verifier-program tag-60 instruction.

   Tag 60 has exactly five accounts in order: read-only finalized proof;
   writable pool; writable canonical nullifier PDA; writable payer signer; and
   executable System Program. Record the complete compiled instruction and
   account-key lists, not merely this prose description.
3. Sign once. Record the transaction signature, recent blockhash, last valid
   height, SHA-256 of the serialized message, and SHA-256 of the complete wire
   transaction.
4. Pass those exact signed bytes to `simulateTransaction` with
   `sigVerify=true`, `replaceRecentBlockhash=false`, finalized commitment, and
   the snapshot slot as `minContextSlot`. Require `err=null`,
   `unitsConsumed < 1_400_000`, the expected CPI path, and no writes to the
   proof, pool, or nullifier accounts. Refetch and compare their raw hashes.
5. Recheck the frozen release/SBF/proof hashes and the coherent account
   predicates. Do not refresh the blockhash or signatures of this candidate.

If the candidate expires before it has ever been sent, record it as a discarded
pre-submission attempt, destroy its authority to proceed, then build, sign, and
simulate a wholly new candidate. A new blockhash always means a new candidate
and a new simulation. The simulated wire SHA-256 and submitted wire SHA-256
must therefore be identical for the candidate that is eventually sent.

### Phase 5: submit, finalize, and verify

1. Submit the exact signed bytes that passed simulation. Record the wire hash
   before the RPC call. After the first send or any ambiguous response, never
   create a new signature automatically. Query that known signature on both
   RPCs and, if necessary, rebroadcast only the byte-identical signed bytes.
   If it is definitively expired without landing, abort for investigation; do
   not silently resign or move to another pool/proof/nullifier statement.
2. Poll the known signature until `finalized`; fail if `err` is non-null.
3. Fetch `getTransaction` at finalized commitment. Require the exact version,
   fee payer, message hash, program id, top-level instructions, tag-60 account
   order, and `meta.err=null`. Record fee, slot, block time, CU consumed, and
   decoded inner instructions; require CU below 1,400,000.
4. In a finalized coherent read at or after the transaction slot, require:

   - the pool owner and length are unchanged, sequence advanced exactly once,
     and anchor equals the frozen output anchor;
   - the nullifier owner is the verifier program, its length is 72, and its
     magic, version, pool bytes, and nullifier bytes are exact; and
   - the proof account remains sealed and byte-identical.

### Phase 6: post-finalization teeth

After capturing raw post-state hashes, simulate but never submit four negative
transactions against the finalized state:

1. the duplicate tag-60 spend, requiring the exact duplicate-nullifier error
   and unchanged pool, nullifier, and proof hashes;
2. `InitProof` against the sealed proof account;
3. `UploadChunk` against the sealed proof account; and
4. `FinalizeProof` against the sealed proof account.

Each sealed-proof mutation must return the expected exact rejection and leave
the complete proof-account SHA-256 unchanged. Record each simulation's signed
message/wire hash, error object, logs, context slot, and before/after account
hashes. Simulation success is never release evidence for the positive claim;
these are only post-finalization negative teeth.

### Phase 7: evidence and independent reconciliation

Write `results/stage2/profile23_mainnet_beta_finalized.json`. Its schema must
include every path listed by the readiness artifact's
`evidence_schema_required_fields`. The following abbreviated nesting is
normative; omitted values are blockers, not permission to delete fields:

```json
{
  "schema_version": 1,
  "generated_at_utc": "<RFC3339>",
  "source_commit": "<40-hex commit>",
  "network": "mainnet-beta",
  "mainnet_genesis_hash": "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2dYd",
  "finalized_at_utc": "<RFC3339>",
  "program_id": "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue",
  "primary_rpc": {
    "origin_redacted": "https://provider.example/<redacted>",
    "genesis_hash": "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2dYd",
    "snapshot_context_slot": 0
  },
  "independent_rpc": {
    "origin_redacted": "https://different.example/<redacted>",
    "genesis_hash": "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2dYd"
  },
  "setup_transactions": [
    {"purpose": "<deploy|freeze|pool-create|pool-init|proof-create|proof-write|proof-finalize>", "signature": "<base58>", "finalized_slot": 0}
  ],
  "deployment": {
    "programdata_address": "<base58>",
    "programdata_max_len": 6870048,
    "programdata_raw_sha256": "<hex>",
    "deployed_code_bytes": 6870048,
    "deployed_code_sha256": "<hex>",
    "upgrade_authority": null,
    "deploy_signatures": ["<base58>"],
    "deploy_finalized_slots": [0],
    "freeze_signature": null,
    "freeze_finalized_slot": null
  },
  "release": {
    "certificate_sha256": "<hex>",
    "proof_sidecar_sha256": "<hex>",
    "proof_sha256": "<hex>",
    "proof_bytes": 61599,
    "sbf_sha256": "<hex>"
  },
  "proof_account": {
    "address": "<base58>",
    "owner": "<base58>",
    "executable": false,
    "data_len": 0,
    "raw_data_sha256": "<hex>",
    "header_magic_hex": "<hex>",
    "declared_proof_len": 61599,
    "authority_is_zero": true,
    "payload_sha256": "<hex>"
  },
  "transaction": {
    "signature": "<base58>",
    "version": "legacy-or-v0",
    "fee_payer": "<base58>",
    "recent_blockhash": "<base58>",
    "last_valid_block_height": 0,
    "message_sha256": "<hex>",
    "wire_sha256": "<hex>",
    "simulated_wire_sha256": "<same hex>",
    "submitted_wire_sha256": "<same hex>",
    "simulated_and_submitted_wire_identical": true,
    "simulation_context_slot": 0,
    "simulation_err": null,
    "simulation_units_consumed": 0,
    "simulation_logs_sha256": "<hex>",
    "attempt_ledger": [],
    "compute_unit_limit": 1400000,
    "heap_frame_bytes": 262144,
    "compute_unit_price_micro_lamports": 0,
    "top_level_instructions": [],
    "tag60_accounts": [],
    "observed_inner_cpi_path": "<create_account|transfer_allocate_assign|allocate_assign|program_owned_zeroed>",
    "meta_err": null,
    "fee_lamports": 0,
    "compute_units_consumed": 0,
    "slot": 0,
    "block_time": 0
  },
  "pool": {
    "address": "<base58>", "owner": "<base58>", "data_len": 0,
    "before_raw_sha256": "<hex>", "after_raw_sha256": "<hex>",
    "sequence_before": 0, "sequence_after": 1,
    "anchor_before": "<hex>", "anchor_after": "<hex>"
  },
  "nullifier": {
    "address": "<base58>", "bump": 0,
    "prestate_kind": "<accepted enum>", "prestate_owner": null,
    "prestate_lamports": 0, "prestate_data_len": 0,
    "prestate_raw_sha256": "<hex-or-null>",
    "after_owner": "<base58>", "after_data_len": 72,
    "after_raw_sha256": "<hex>", "after_magic_hex": "4153504e",
    "after_version": 1, "after_pool": "<base58>",
    "after_value": "<hex>"
  },
  "negative_simulations": {
    "duplicate_spend": {
      "message_sha256": "<hex>", "wire_sha256": "<hex>",
      "context_slot": 0, "exact_error": "<RPC error object>",
      "logs_sha256": "<hex>", "state_unchanged": true,
      "pool_raw_sha256_before": "<hex>", "pool_raw_sha256_after": "<same hex>",
      "nullifier_raw_sha256_before": "<hex>", "nullifier_raw_sha256_after": "<same hex>",
      "proof_raw_sha256_before": "<hex>", "proof_raw_sha256_after": "<same hex>"
    },
    "sealed_init_proof": {
      "message_sha256": "<hex>", "wire_sha256": "<hex>",
      "context_slot": 0, "exact_error": "<RPC error object>", "logs_sha256": "<hex>"
    },
    "sealed_upload_chunk": {
      "message_sha256": "<hex>", "wire_sha256": "<hex>",
      "context_slot": 0, "exact_error": "<RPC error object>", "logs_sha256": "<hex>"
    },
    "sealed_finalize_proof": {
      "message_sha256": "<hex>", "wire_sha256": "<hex>",
      "context_slot": 0, "exact_error": "<RPC error object>", "logs_sha256": "<hex>"
    },
    "proof_raw_sha256_before": "<hex>",
    "proof_raw_sha256_after": "<same hex>"
  },
  "independent_reconciliation": {
    "checked_at_utc": "<RFC3339>",
    "provider_origin_redacted": "https://different.example/<redacted>",
    "context_slot": 0,
    "at_or_after_transaction_slot": true,
    "all_predicates_match": true
  },
  "explorer_url": "https://explorer.solana.com/tx/<signature>?cluster=mainnet-beta"
}
```

The independent checker must verify the audit RPC's genesis hash, wait until it
can serve a finalized context slot at least equal to the atomic transaction's
slot, and refetch the transaction, Program, ProgramData, proof, pool, and
nullifier from that provider. It recomputes every raw hash, payload/code hash,
decoded predicate, message hash, instruction/account list, and CU/fee field.
The provider hostname and credentials must differ from the primary provider;
both origins are stored only in redacted form. The paper and announcement may
link the signature only after this reconciliation is green.

### Retry and rollback law

- Before any setup retry, reconcile the known signature and deterministic
  target account. Deployment and chunk upload may resume only from verified
  bytes; they may never switch the frozen pool or proof statement.
- A final candidate that expires before its first send may be discarded and
  replaced only after the replacement is freshly signed and simulated. After
  its first send, only status queries and byte-identical rebroadcasts are
  permitted.
- Simulations must not change state. Any before/after hash drift is a release
  blocker even if the RPC reports success.
- An immutable program has no binary rollback. Pool initialization and proof
  rent may be stranded if setup later aborts. A successful tag-60 pool and
  nullifier transition is intentionally irreversible.
- A retained upgrade authority can change future program code, but a binary
  rollback cannot undo an already committed pool or nullifier state.

## Current external blockers

At the time this runbook was repinned, the local tag-62/tag-63/program-id
release certificate was green. The live path still requires:

- a reviewed live executor implementing the sequence above;
- release-gate coverage for the frozen live envelope and both accepted
  prefunded-system nullifier-PDA CPI variants;
- a dedicated paid/private mainnet-beta RPC;
- a genuinely independent second mainnet-beta RPC provider;
- sufficient funded payer balance for the conservative deployment/setup peak;
- an explicit upgrade-authority decision;
- fresh real pool/proof-account keypairs, with the proof mined and released
  against the pool pubkey before either account is created; and
- the resulting finalized signature and independent evidence reconciliation.

No placeholder, simulation signature, local-validator signature, devnet
signature, or manually typed explorer URL satisfies these blockers.
